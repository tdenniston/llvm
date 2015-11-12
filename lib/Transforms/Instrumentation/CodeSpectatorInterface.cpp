#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h" // for itostr function
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace llvm;

// see
// http://llvm.org/docs/ProgrammersManual.html#the-debug-macro-and-debug-option
// on how to use debugging infrastructure in LLVM
// also used by STATISTIC macro, so need to define this before using STATISTIC
#define DEBUG_TYPE "csi-func"

// XXX: Not sure how to turn these on yet
STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");
STATISTIC(NumAccessesWithBadSize, "Number of accesses with bad size");

static const char *const CsiModuleCtorName = "csi.module_ctor";
static const char *const CsiModuleInitName = "__csi_module_init";
static const char *const CsiModuleIdName = "__csi_module_id";
static const char *const CsiInitCtorName = "csi.init_ctor";
static const char *const CsiInitName = "__csi_init";
// See llvm/tools/clang/lib/CodeGen/CodeGenModule.h:
static const int CsiModuleCtorPriority = 65535,
    CsiInitCtorPriority = 65534;

namespace {

struct CodeSpectatorInterface : public FunctionPass {
  static char ID;

  CodeSpectatorInterface() : FunctionPass(ID), CsiInitialized(false), NextBasicBlockId(0) {}
  const char *getPassName() const override;
  bool doInitialization(Module &M) override;
  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;

  // not overriding doFinalization

private:
  int getNumBytesAccessed(Value *Addr, const DataLayout &DL);
  // initialize CSI instrumentation functions for load and store
  void initializeLoadStoreCallbacks(Module &M);
  // initialize CSI instrumentation functions for function entry and exit
  void initializeFuncCallbacks(Module &M);
  // Basic block entry and exit instrumentation
  void initializeBasicBlockCallbacks(Module &M);
  // actually insert the instrumentation call
  bool instrumentLoadOrStore(inst_iterator Iter, const DataLayout &DL);
  // instrument a call to memmove, memcpy, or memset
  void instrumentMemIntrinsic(inst_iterator I);
  bool instrumentBasicBlock(BasicBlock &BB);
  bool FunctionCallsFunction(Function *F, Function *G);
  bool ShouldNotInstrumentFunction(Function &F);
  void InitializeCsi(Module &M);
  uint64_t GetNextBasicBlockId();

  CallGraph *CG;
  bool CsiInitialized;
  GlobalVariable *ModuleId;
  uint64_t NextBasicBlockId;
  Function *CsiModuleCtorFunction;

  Function *CsiBeforeRead;
  Function *CsiAfterRead;
  Function *CsiBeforeWrite;
  Function *CsiAfterWrite;

  Function *CsiFuncEntry;
  Function *CsiFuncExit;
  Function *CsiBBEntry, *CsiBBExit;
  Function *MemmoveFn, *MemcpyFn, *MemsetFn;

  Type *IntptrTy;
  StructType *CsiIdType;
}; //struct CodeSpectatorInterface
} //namespace

// the address matters but not the init value
char CodeSpectatorInterface::ID = 0;
INITIALIZE_PASS(CodeSpectatorInterface, "CSI-func", "CodeSpectatorInterface function pass",
                false, false)

const char *CodeSpectatorInterface::getPassName() const {
  return "CodeSpectatorInterface";
}

FunctionPass *llvm::createCodeSpectatorInterfacePass() {
  return new CodeSpectatorInterface();
}

/**
 * initialize the declaration of function call instrumentation functions
 *
 * void __csi_func_entry(void *parentReturnAddress, char *funcName);
 * void __csi_func_exit();
 */
void CodeSpectatorInterface::initializeFuncCallbacks(Module &M) {
  IRBuilder<> IRB(M.getContext());
  CsiFuncEntry = checkCsiInterfaceFunction(M.getOrInsertFunction(
      "__csi_func_entry", IRB.getVoidTy(), IRB.getInt8PtrTy(), IRB.getInt8PtrTy(), nullptr));
  CsiFuncExit = checkCsiInterfaceFunction(
      M.getOrInsertFunction("__csi_func_exit", IRB.getVoidTy(), nullptr));
}

void CodeSpectatorInterface::initializeBasicBlockCallbacks(Module &M) {
  IRBuilder<> IRB(M.getContext());
  CsiBBEntry = checkCsiInterfaceFunction(M.getOrInsertFunction(
      "__csi_bb_entry", IRB.getVoidTy(), CsiIdType, nullptr));
  CsiBBExit = checkCsiInterfaceFunction(
      M.getOrInsertFunction("__csi_bb_exit", IRB.getVoidTy(), nullptr));
}

/**
 * initialize the declaration of instrumentation functions
 *
 * void __csi_before_load(void *addr, int num_bytes, int attr);
 *
 * where num_bytes = 1, 2, 4, 8.
 *
 * Presumably aligned / unaligned accesses are specified by the attr
 */
void CodeSpectatorInterface::initializeLoadStoreCallbacks(Module &M) {

  IRBuilder<> IRB(M.getContext());
  Type *RetType = IRB.getVoidTy();            // return void
  Type *AddrType = IRB.getInt8PtrTy();        // void *addr
  Type *NumBytesType = IRB.getInt32Ty();      // int num_bytes
  Type *AttrType = IRB.getInt32Ty();          // int attr

  // Initialize the instrumentation for reads, writes
  // NOTE: nullptr is a new C++11 construct; denote a null pointer
  // here, just used to denote end of args;

  // void __csi_before_load(void *addr, int num_bytes, int attr);
  CsiBeforeRead = checkCsiInterfaceFunction(
      M.getOrInsertFunction("__csi_before_load", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

  // void __csi_after_load(void *addr, int num_bytes, int attr);
  SmallString<32> AfterReadName("__csi_after_load");
  CsiAfterRead = checkCsiInterfaceFunction(
      M.getOrInsertFunction("__csi_after_load", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

  // void __csi_before_store(void *addr, int num_bytes, int attr);
  CsiBeforeWrite = checkCsiInterfaceFunction(
      M.getOrInsertFunction("__csi_before_store", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

  // void __csi_after_store(void *addr, int num_bytes, int attr);
  CsiAfterWrite = checkCsiInterfaceFunction(
      M.getOrInsertFunction("__csi_after_store", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

  MemmoveFn = checkCsiInterfaceFunction(
      M.getOrInsertFunction("memmove", IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                            IRB.getInt8PtrTy(), IntptrTy, nullptr));
  MemcpyFn = checkCsiInterfaceFunction(
      M.getOrInsertFunction("memcpy", IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                            IRB.getInt8PtrTy(), IntptrTy, nullptr));
  MemsetFn = checkCsiInterfaceFunction(
      M.getOrInsertFunction("memset", IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                            IRB.getInt32Ty(), IntptrTy, nullptr));
}

int CodeSpectatorInterface::getNumBytesAccessed(Value *Addr,
                                                const DataLayout &DL) {
  Type *OrigPtrTy = Addr->getType();
  Type *OrigTy = cast<PointerType>(OrigPtrTy)->getElementType();
  assert(OrigTy->isSized());
  uint32_t TypeSize = DL.getTypeStoreSizeInBits(OrigTy);
  if (TypeSize != 8  && TypeSize != 16 && TypeSize != 32 && TypeSize != 64 && TypeSize != 128) {
    DEBUG_WITH_TYPE("csi-func",
        errs() << "Bad size " << TypeSize << " at addr " << Addr << "\n");
    NumAccessesWithBadSize++;
    return -1;
  }
  return TypeSize / 8;
}

bool CodeSpectatorInterface::instrumentLoadOrStore(inst_iterator Iter,
                                                   const DataLayout &DL) {

  DEBUG_WITH_TYPE("csi-func",
      errs() << "CSI_func: instrument instruction " << *Iter << "\n");

  Instruction *I = &(*Iter);
  // takes pointer to Instruction and inserts before the instruction
  IRBuilder<> IRB(I);
  bool IsWrite = isa<StoreInst>(I);
  Value *Addr = IsWrite ?
      cast<StoreInst>(I)->getPointerOperand()
      : cast<LoadInst>(I)->getPointerOperand();

  int NumBytes = getNumBytesAccessed(Addr, DL);
  Type *AddrType = IRB.getInt8PtrTy();

  if (NumBytes == -1) return false; // size that we don't recognize

  /* XXX: This deals ww/ Alignment; come back later
  const unsigned Alignment = IsWrite ?
      cast<StoreInst>(I)->getAlignment() : cast<LoadInst>(I)->getAlignment();

  Type *OrigTy = cast<PointerType>(Addr->getType())->getElementType();
  const uint32_t TypeSize = DL.getTypeStoreSize(OrigTy);
  if (Alignment == 0 || Alignment >= 8 || (Alignment % TypeSize) == 0)
    OnAccessFunc = IsWrite ? TsanWrite[Idx] : TsanRead[Idx];
  else
    OnAccessFunc = IsWrite ? TsanUnalignedWrite[Idx] : TsanUnalignedRead[Idx];
  */
  if(IsWrite) {
    StoreInst *S = cast<StoreInst>(I);
    Type *SType = S->getValueOperand()->getType();

    DEBUG_WITH_TYPE("csi-func",
        errs() << "CSI_func: creating call to before store for "
               << NumBytes << " bytes and type " << SType << "\n");
    IRB.CreateCall(CsiBeforeWrite,
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)}); // XXX: use 0 for attr for now; FIXME

    // The iterator currently points between the inserted instruction and the
    // store instruction. We now want to insert an instruction after the store
    // instruction.
    Iter++;
    IRB.SetInsertPoint(&*Iter);

    DEBUG_WITH_TYPE("csi-func",
        errs() << "CSI_func: creating call to after store for "
               << NumBytes << " bytes\n");
    IRB.CreateCall(CsiAfterWrite,
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)});
    NumInstrumentedWrites++;

  } else { // is read
    LoadInst *L = cast<LoadInst>(I);
    Type *LType = L->getType();

    DEBUG_WITH_TYPE("csi-func",
        errs() << "CSI_func: creating call to before load for "
               << NumBytes << " bytes and type " << LType << "\n");
    IRB.CreateCall(CsiBeforeRead,
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)});

    // The iterator currently points between the inserted instruction and the
    // store instruction. We now want to insert an instruction after the store
    // instruction.
    Iter++;
    IRB.SetInsertPoint(&*Iter);

    DEBUG_WITH_TYPE("csi-func",
        errs() << "CSI_func: creating call to after load for "
               << NumBytes << " bytes\n");
    IRB.CreateCall(CsiAfterRead,
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)});
    NumInstrumentedReads++;
  }

  return true;
}

// If a memset intrinsic gets inlined by the code gen, we will miss races on it.
// So, we either need to ensure the intrinsic is not inlined, or instrument it.
// We do not instrument memset/memmove/memcpy intrinsics (too complicated),
// instead we simply replace them with regular function calls, which are then
// intercepted by the run-time.
// Since our pass runs after everyone else, the calls should not be
// replaced back with intrinsics. If that becomes wrong at some point,
// we will need to call e.g. __csi_memset to avoid the intrinsics.
void CodeSpectatorInterface::instrumentMemIntrinsic(inst_iterator Iter) {
  Instruction *I = &(*Iter);
  IRBuilder<> IRB(I);
  if (MemSetInst *M = dyn_cast<MemSetInst>(I)) {
    IRB.CreateCall(
        MemsetFn,
        {IRB.CreatePointerCast(M->getArgOperand(0), IRB.getInt8PtrTy()),
         IRB.CreateIntCast(M->getArgOperand(1), IRB.getInt32Ty(), false),
         IRB.CreateIntCast(M->getArgOperand(2), IntptrTy, false)});
    I->eraseFromParent();
  } else if (MemTransferInst *M = dyn_cast<MemTransferInst>(I)) {
    IRB.CreateCall(
        isa<MemCpyInst>(M) ? MemcpyFn : MemmoveFn,
        {IRB.CreatePointerCast(M->getArgOperand(0), IRB.getInt8PtrTy()),
         IRB.CreatePointerCast(M->getArgOperand(1), IRB.getInt8PtrTy()),
         IRB.CreateIntCast(M->getArgOperand(2), IntptrTy, false)});
    I->eraseFromParent();
  }
}

uint64_t CodeSpectatorInterface::GetNextBasicBlockId() {
  return NextBasicBlockId++;
}

bool CodeSpectatorInterface::instrumentBasicBlock(BasicBlock &BB) {
  IRBuilder<> IRB(BB.getFirstInsertionPt());
  Value *Id = IRB.CreateInsertValue(UndefValue::get(CsiIdType), IRB.CreateLoad(ModuleId), 0);
  Id = IRB.CreateInsertValue(Id, IRB.getInt64(GetNextBasicBlockId()), 1);
  IRB.CreateCall(CsiBBEntry, {Id});
  TerminatorInst *TI = BB.getTerminator();
  IRB.SetInsertPoint(TI);
  IRB.CreateCall(CsiBBExit, {});
  return true;
}

bool CodeSpectatorInterface::doInitialization(Module &M) {
  DEBUG_WITH_TYPE("csi-func", errs() << "CSI_func: doInitialization" << "\n");

  IntptrTy = M.getDataLayout().getIntPtrType(M.getContext());

  DEBUG_WITH_TYPE("csi-func",
      errs() << "CSI_func: doInitialization done" << "\n");
  return true;
}

void CodeSpectatorInterface::InitializeCsi(Module &M) {
  LLVMContext &C = M.getContext();
  IntegerType *Int32Ty = IntegerType::get(C, 32), *Int64Ty = IntegerType::get(C, 64);

  CsiIdType = StructType::create({Int32Ty, Int64Ty}, "__csi_id_t");
  ModuleId = new GlobalVariable(M, Int32Ty, false, GlobalValue::InternalLinkage, ConstantInt::get(Int32Ty, 0), CsiModuleIdName);
  assert(ModuleId);

  initializeFuncCallbacks(M);
  initializeLoadStoreCallbacks(M);
  initializeBasicBlockCallbacks(M);

  CG = &getAnalysis<CallGraphWrapperPass>().getCallGraph();

  uint64_t NumBasicBlocks = 0;
  for (Function &F : M) {
    if (ShouldNotInstrumentFunction(F)) continue;
    NumBasicBlocks += F.size();
  }

  // Add CSI global constructor, which calls module init.
  Function *Ctor = Function::Create(
      FunctionType::get(Type::getVoidTy(M.getContext()), false),
      GlobalValue::InternalLinkage, CsiModuleCtorName, &M);
  BasicBlock *CtorBB = BasicBlock::Create(M.getContext(), "", Ctor);
  IRBuilder<> IRB(ReturnInst::Create(M.getContext(), CtorBB));

  StructType *CsiModuleInfoType = StructType::create({Int32Ty, Int64Ty}, "__csi_module_info_t");
  SmallVector<Type *, 4> InitArgTypes({CsiModuleInfoType});
  Function *InitFunction = dyn_cast<Function>(M.getOrInsertFunction(CsiModuleInitName, FunctionType::get(IRB.getVoidTy(), InitArgTypes, false)));
  assert(InitFunction);

  Value *Info = IRB.CreateInsertValue(UndefValue::get(CsiModuleInfoType), IRB.CreateLoad(ModuleId), 0);
  Info = IRB.CreateInsertValue(Info, IRB.getInt64(NumBasicBlocks), 1);
  CallInst *Call = IRB.CreateCall(InitFunction, {Info});

  appendToGlobalCtors(M, Ctor, CsiModuleCtorPriority);

  CallGraphNode *CNCtor = CG->getOrInsertFunction(Ctor);
  CallGraphNode *CNFunc = CG->getOrInsertFunction(InitFunction);
  CNCtor->addCalledFunction(Call, CNFunc);

  CsiInitialized = true;
}

void CodeSpectatorInterface::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<CallGraphWrapperPass>();
}

// Recursively determine if F calls G. Return true if so. Conservatively, if F makes
// any internal indirect function calls, assume it calls G.
bool CodeSpectatorInterface::FunctionCallsFunction(Function *F, Function *G) {
  assert(F && G && CG);
  CallGraphNode *CGN = (*CG)[F];
  // Assume external functions cannot make calls to internal functions.
  if (!F->hasLocalLinkage() && G->hasLocalLinkage()) return false;
  // Assume function declarations won't make calls to internal
  // functions. TODO: This may not be correct in general.
  if (F->isDeclaration()) return false;
  for (CallGraphNode::iterator it = CGN->begin(), ite = CGN->end(); it != ite; ++it) {
    Function *Called = it->second->getFunction();
    if (Called == NULL) {
      // Indirect call
      return true;
    } else if (Called == G) {
      return true;
    } else if (G->hasLocalLinkage() && !Called->hasLocalLinkage()) {
      // Assume external functions cannot make calls to internal functions.
      continue;
    }
  }
  for (CallGraphNode::iterator it = CGN->begin(), ite = CGN->end(); it != ite; ++it) {
    Function *Called = it->second->getFunction();
    if (FunctionCallsFunction(Called, G)) return true;
  }
  return false;
}

bool CodeSpectatorInterface::ShouldNotInstrumentFunction(Function &F) {
    Module &M = *F.getParent();
    if (F.hasName() && F.getName() == CsiModuleCtorName) {
        return true;
    }
    // Don't instrument functions that will run before or
    // simultaneously with CSI ctors.
    GlobalVariable *GV = M.getGlobalVariable("llvm.global_ctors");
    if (GV == nullptr) return false;
    ConstantArray *CA = cast<ConstantArray>(GV->getInitializer());
    for (Use &OP : CA->operands()) {
        if (isa<ConstantAggregateZero>(OP)) continue;
        ConstantStruct *CS = cast<ConstantStruct>(OP);

        if (Function *CF = dyn_cast<Function>(CS->getOperand(1))) {
            uint64_t Priority = dyn_cast<ConstantInt>(CS->getOperand(0))->getLimitedValue();
            if (Priority <= CsiModuleCtorPriority) {
                return CF->getName() == F.getName() ||  FunctionCallsFunction(CF, &F);
            }
        }
    }
    // false means do instrument it.
    return false;
}

bool CodeSpectatorInterface::runOnFunction(Function &F) {
  // This is required to prevent instrumenting the call to
  // __csi_module_init from within the module constructor.
  if (!CsiInitialized) {
    Module &M = *F.getParent();
    InitializeCsi(M);
  }

  if (ShouldNotInstrumentFunction(F)) {
      return false;
  }

  DEBUG_WITH_TYPE("csi-func",
                  errs() << "CSI_func: run on function " << F.getName() << "\n");

  SmallVector<inst_iterator, 8> MemoryAccesses;
  SmallVector<inst_iterator, 8> RetVec;
  SmallVector<inst_iterator, 8> MemIntrinsics;
  bool Modified = false;
  const DataLayout &DL = F.getParent()->getDataLayout();

  // Traverse all instructions in a function and insert instrumentation
  // on load & store
  for (inst_iterator I = inst_begin(F); I != inst_end(F); ++I) {
    // We need the Instruction Iterator to modify the code
    if (isa<LoadInst>(*I) || isa<StoreInst>(*I)) {
      MemoryAccesses.push_back(I);
    } else if (isa<ReturnInst>(*I)) {
      RetVec.push_back(I);
    } else if (isa<CallInst>(*I) || isa<InvokeInst>(*I)) {
      if (isa<MemIntrinsic>(&(*I)))
        MemIntrinsics.push_back(I);
    }
  }

  // Do this work in a separate loop after copying the iterators so that we
  // aren't modifying the list as we're iterating.
  for (inst_iterator I : MemoryAccesses)
    Modified |= instrumentLoadOrStore(I, DL);

  for (inst_iterator I : MemIntrinsics)
    instrumentMemIntrinsic(I);

  // Instrument function entry/exit points.
  IRBuilder<> IRB(F.getEntryBlock().getFirstInsertionPt());
  Value *FunctionName = IRB.CreateGlobalStringPtr(F.getName());
  Value *ReturnAddress = IRB.CreateCall(
        Intrinsic::getDeclaration(F.getParent(), Intrinsic::returnaddress),
        IRB.getInt32(0));
  IRB.CreateCall(CsiFuncEntry, {ReturnAddress, FunctionName});

  for (inst_iterator I : RetVec) {
      Instruction *RetInst = &(*I);
      IRBuilder<> IRBRet(RetInst);
      IRBRet.CreateCall(CsiFuncExit, {});
  }
  Modified = true;

  // Instrument basic blocks
  for (BasicBlock &BB : F) {
    Modified |= instrumentBasicBlock(BB);
  }

  if(Modified) {
    DEBUG_WITH_TYPE("csi-func",
        errs() << "CSI_func: modified function " << F.getName() << "\n");
  }
  return Modified;
}

// End of compile-time pass
// ------------------------------------------------------------------------
// LTO (link-time) pass

namespace {

struct CodeSpectatorInterfaceLT : public ModulePass {
  static char ID;

  CodeSpectatorInterfaceLT() : ModulePass(ID), moduleId(0) {}
  const char *getPassName() const override;
  bool runOnModule(Module &M) override;

private:
  unsigned moduleId;
  Function *CsiCtorFunction;
}; //struct CodeSpectatorInterfaceLT

} // namespace

char CodeSpectatorInterfaceLT::ID = 0;
INITIALIZE_PASS(CodeSpectatorInterfaceLT, "CSI-lt", "CodeSpectatorInterface link-time pass",
                false, false)

ModulePass *llvm::createCodeSpectatorInterfaceLTPass() {
  return new CodeSpectatorInterfaceLT();
}

const char *CodeSpectatorInterfaceLT::getPassName() const {
  return "CodeSpectatorInterfaceLT";
}

bool CodeSpectatorInterfaceLT::runOnModule(Module &M) {
  LLVMContext &C = M.getContext();
  StructType *CsiInfoType = StructType::create({IntegerType::get(C, 32)},
                                               "__csi_info_t");

  for (GlobalVariable &GV : M.getGlobalList()) {
    if (GV.hasName() && GV.getName().startswith(CsiModuleIdName)) {
      assert(GV.hasInitializer());
      Constant *UniqueModuleId = ConstantInt::get(GV.getInitializer()->getType(), moduleId++);
      GV.setInitializer(UniqueModuleId);
      GV.setConstant(true);
    }
  }

  // Add call to whole-program/tool init function.
  Function *Ctor = Function::Create(
      FunctionType::get(Type::getVoidTy(M.getContext()), false),
      GlobalValue::InternalLinkage, CsiInitCtorName, &M);
  BasicBlock *CtorBB = BasicBlock::Create(M.getContext(), "", Ctor);
  IRBuilder<> IRB(ReturnInst::Create(M.getContext(), CtorBB));

  const uint32_t NumModules = moduleId;
  SmallVector<Type *, 4> InitArgTypes({CsiInfoType});
  SmallVector<Value *, 4> InitArgs({ConstantStruct::get(CsiInfoType, {IRB.getInt32(NumModules)})});

  Constant *InitFunction = M.getOrInsertFunction(CsiInitName, FunctionType::get(IRB.getVoidTy(), InitArgTypes, false));
  assert(InitFunction);
  IRB.CreateCall(InitFunction, InitArgs);

  // Ensure whole-program init is called before module init.
  // TODO: do all targets support this?
  appendToGlobalCtors(M, Ctor, CsiInitCtorPriority);

  return true;
}
