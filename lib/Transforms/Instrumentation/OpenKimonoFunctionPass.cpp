#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h" // for itostr function
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

// XXX: Just about to try to compile
// Still need to fix "checkOkInterfaceFunction

using namespace llvm;

// see
// http://llvm.org/docs/ProgrammersManual.html#the-debug-macro-and-debug-option
// on how to use debugging infrastructure in LLVM
// also used by STATISTIC macro, so need to define this before using STATISTIC
#define DEBUG_TYPE "ok-func"

// XXX: Not sure how to turn these on yet
STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");
STATISTIC(NumAccessesWithBadSize, "Number of accesses with bad size");

static const char *const OkModuleCtorName = "ok.module_ctor";
static const char *const OkInitName = "__ok_init";

namespace {

struct OpenKimonoFunctionPass : public FunctionPass {
  static char ID;

  OpenKimonoFunctionPass() : FunctionPass(ID) {}
  const char *getPassName() const override;
  bool doInitialization(Module &M) override;
  bool runOnFunction(Function &F) override;
  // not overriding doFinalization

private:
  size_t getNumBytesAccessed(Value *Addr, const DataLayout &DL);
  // initialize OK instrumentation functions for load and store
  void initializeLoadStoreCallbacks(Module &M);
  // initialize OK instrumentation functions for function entry and exit
  void initializeFuncCallbacks(Module &M);
  // actually insert the instrumentation call
  bool instrumentLoadOrStore(inst_iterator Iter, const DataLayout &DL);
  // Instrument basic block entry/exit
  bool instrumentBasicBlock(BasicBlock &BB);

  Function *OkCtorFunction;

  Function *OkBeforeRead;
  Function *OkAfterRead;
  Function *OkBeforeWrite;
  Function *OkAfterWrite;

  Function *OkFuncEntry;
  Function *OkFuncExit;
}; //struct OpenKimonoFunctionPass

} //namespace

// the address matters but not the init value
char OpenKimonoFunctionPass::ID = 0;
INITIALIZE_PASS(OpenKimonoFunctionPass, "OK-func", "OpenKimono function pass",
                false, false)

// XXX for now let's always register it; move it to commnad line option later
/*
static RegisterPass<OpenKimonoFunctionPass>
OkFunctonPass("ok-func", "OpenKimono function pass", false, false);
*/

const char *OpenKimonoFunctionPass::getPassName() const {
  return "OpenKimonoFunctionPass";
}

FunctionPass *llvm::createOpenKimonoFunctionPass() {
  return new OpenKimonoFunctionPass();
}

/**
 * initialize the declaration of function call instrumentation functions
 *
 * void __ok_func_entry(void *parentReturnAddress, char *funcName);
 * void __ok_func_exit();
 */
void OpenKimonoFunctionPass::initializeFuncCallbacks(Module &M) {
  IRBuilder<> IRB(M.getContext());
  OkFuncEntry = checkSanitizerInterfaceFunction(M.getOrInsertFunction(
      "__ok_func_entry", IRB.getVoidTy(), IRB.getInt8PtrTy(), IRB.getInt8PtrTy(), nullptr));
  OkFuncExit = checkSanitizerInterfaceFunction(
      M.getOrInsertFunction("__ok_func_exit", IRB.getVoidTy(), nullptr));
}

/**
 * initialize the declaration of instrumentation functions
 *
 * void __ok_before_load(void *addr, int num_bytes, int attr);
 *
 * where num_bytes = 1, 2, 4, 8.
 *
 * Presumably aligned / unaligned accesses are specified by the attr
 */
void OpenKimonoFunctionPass::initializeLoadStoreCallbacks(Module &M) {

  IRBuilder<> IRB(M.getContext());
  Type *RetType = IRB.getVoidTy();            // return void
  Type *AddrType = IRB.getInt8PtrTy();        // void *addr
  Type *NumBytesType = IRB.getInt32Ty();      // int num_bytes
  Type *AttrType = IRB.getInt32Ty();          // int attr

  // Initialize the instrumentation for reads, writes
  // NOTE: nullptr is a new C++11 construct; denote a null pointer
  // here, just used to denote end of args;

  // void __ok_before_load(void *addr, int num_bytes, int attr);
  OkBeforeRead = checkOkInterfaceFunction(
      M.getOrInsertFunction("__ok_before_load", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

  // void __ok_after_load(void *addr, int num_bytes, int attr);
  SmallString<32> AfterReadName("__ok_after_load");
  OkAfterRead = checkOkInterfaceFunction(
      M.getOrInsertFunction("__ok_after_load", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

  // void __ok_before_store(void *addr, int num_bytes, int attr);
  OkBeforeWrite = checkSanitizerInterfaceFunction(
      M.getOrInsertFunction("__ok_before_store", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

  // void __ok_after_store(void *addr, int num_bytes, int attr);
  OkAfterWrite = checkOkInterfaceFunction(
      M.getOrInsertFunction("__ok_after_store", RetType,
                            AddrType, NumBytesType, AttrType, nullptr));

}

size_t OpenKimonoFunctionPass::getNumBytesAccessed(Value *Addr,
                                                   const DataLayout &DL) {
  Type *OrigPtrTy = Addr->getType();
  Type *OrigTy = cast<PointerType>(OrigPtrTy)->getElementType();
  assert(OrigTy->isSized());
  uint32_t TypeSize = DL.getTypeStoreSizeInBits(OrigTy);
  if (TypeSize != 8  && TypeSize != 16 && TypeSize != 32 && TypeSize != 64) {
    DEBUG_WITH_TYPE("ok-func",
        errs() << "Bad size " << TypeSize << " at addr " << Addr << "\n");
    NumAccessesWithBadSize++;
    return -1;
  }
  return TypeSize / 8;
}

bool OpenKimonoFunctionPass::instrumentLoadOrStore(inst_iterator Iter,
                                                   const DataLayout &DL) {

  DEBUG_WITH_TYPE("ok-func",
      errs() << "OK_func: instrument instruction " << *Iter << "\n");

  Instruction *I = &(*Iter);
  // takes pointer to Instruction and inserts before the instruction
  IRBuilder<> IRB(I);
  bool IsWrite = isa<StoreInst>(I);
  Value *Addr = IsWrite ?
      cast<StoreInst>(I)->getPointerOperand()
      : cast<LoadInst>(I)->getPointerOperand();

  size_t NumBytes = getNumBytesAccessed(Addr, DL);
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

    DEBUG_WITH_TYPE("ok-func",
        errs() << "OK_func: creating call to before store for "
               << NumBytes << " bytes and type " << SType << "\n");
    IRB.CreateCall(OkBeforeWrite,
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)}); // XXX: use 0 for attr for now; FIXME
    // move pass the actual store instruction;
    // the inserted instruction doesn't seem to count.
    Iter++;
    IRB.SetInsertPoint(&*Iter);

    DEBUG_WITH_TYPE("ok-func",
        errs() << "OK_func: creating call to after store for "
               << NumBytes << " bytes\n");
    IRB.CreateCall(OkAfterWrite,
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)});
    NumInstrumentedWrites++;

  } else { // is read
    LoadInst *L = cast<LoadInst>(I);
    Type *LType = L->getType();

    DEBUG_WITH_TYPE("ok-func",
        errs() << "OK_func: creating call to before load for "
               << NumBytes << " bytes and type " << LType << "\n");
    IRB.CreateCall(OkBeforeRead,
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)});
    // move pass the actual load instruction;
    // the inserted instruction doesn't seem to count.
    Iter++;
    IRB.SetInsertPoint(&*Iter);

    DEBUG_WITH_TYPE("ok-func",
        errs() << "OK_func: creating call to after load for "
               << NumBytes << " bytes\n");
    IRB.CreateCall(OkAfterRead,
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(NumBytes),
         IRB.getInt32(0)});
    NumInstrumentedReads++;
  }

  return true;
}

bool OpenKimonoFunctionPass::instrumentBasicBlock(BasicBlock &BB) {
  static int id = 0;
  Module &M = *BB.getModule();
  Instruction *Entry = BB.getFirstInsertionPt();
  IRBuilder<> IRB(Entry);

  Type *RetType = IRB.getVoidTy();            // return void
  Type *AddrType = IRB.getInt8PtrTy();        // void *val
  Type *AttrType = IRB.getInt32Ty();          // int attr
  Type *IdType = IRB.getInt32Ty();

  Function *F = checkOkInterfaceFunction(
      M.getOrInsertFunction("__ok_bb_entry", RetType, IdType, AttrType, nullptr));
  IRB.CreateCall(F, {IRB.getInt32(id++), IRB.getInt32(0)});
  return true;
}

bool OpenKimonoFunctionPass::doInitialization(Module &M) {
  DEBUG_WITH_TYPE("ok-func", errs() << "OK_func: doInitialization" << "\n");

  std::tie(OkCtorFunction, std::ignore) = createSanitizerCtorAndInitFunctions(
      M, OkModuleCtorName, OkInitName, /*InitArgTypes=*/{},
      /*InitArgs=*/{});
  appendToGlobalCtors(M, OkCtorFunction, 0);

  initializeFuncCallbacks(M);
  initializeLoadStoreCallbacks(M);
  DEBUG_WITH_TYPE("ok-func",
      errs() << "OK_func: doInitialization done" << "\n");

  return true;
}

bool OpenKimonoFunctionPass::runOnFunction(Function &F) {
  // This is required to prevent instrumenting call to __ok_init from within
  // the module constructor.
  if (&F == OkCtorFunction)
      return false;

  DEBUG_WITH_TYPE("ok-func",
                  errs() << "OK_func: run on function " << F.getName() << "\n");

  SmallVector<Instruction*, 8> AllLoadsAndStores;
  SmallVector<Instruction*, 8> LocalLoadsAndStores;
  SmallVector<inst_iterator, 8> RetVec;
  bool Modified = false, HasCalls = false;
  const DataLayout &DL = F.getParent()->getDataLayout();

  // Traverse all instructions in a function and insert instrumentation
  // on load & store
  for (inst_iterator I = inst_begin(F); I != inst_end(F); ++I) {
    // We need the Instruction Iterator to modify the code
    if (isa<LoadInst>(*I) || isa<StoreInst>(*I)) {
      Modified |= instrumentLoadOrStore(I, DL);
    } else if (isa<ReturnInst>(*I)) {
      RetVec.push_back(I);
    } else if (isa<CallInst>(*I) || isa<InvokeInst>(*I)) {
      // DD: If we decide to track memset, memcpy, etc, we can uncomment the
      // next two lines
      // if (isa<MemIntrinsic>(I))
        // MemIntrinCalls.push_back(&I);

      HasCalls = true;
    }
  }

  for (BasicBlock &BB : F) {
      Modified |= instrumentBasicBlock(BB);
  }

  // Instrument function entry/exit points if there were instrumented accesses.
  if (HasCalls || Modified) {
    IRBuilder<> IRB(F.getEntryBlock().getFirstNonPHI());
    Value *FunctionName = IRB.CreateGlobalStringPtr(F.getName());
    Value *ReturnAddress = IRB.CreateCall(
        Intrinsic::getDeclaration(F.getParent(), Intrinsic::returnaddress),
        IRB.getInt32(0));
    IRB.CreateCall(OkFuncEntry, {ReturnAddress, FunctionName});

    for (inst_iterator I : RetVec) {
      Instruction *RetInst = &(*I);
      IRBuilder<> IRBRet(RetInst);
      IRBRet.CreateCall(OkFuncExit, {});
    }

    Modified = true;
  }

  if(Modified) {
    DEBUG_WITH_TYPE("ok-func",
        errs() << "OK_func: modified function " << F.getName() << "\n");
  }
  return Modified;
}
