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

namespace {

struct OpenKimonoFunctionPass : public FunctionPass {
  static char ID;

  OpenKimonoFunctionPass() : FunctionPass(ID) {}
  const char *getPassName() const override;
  bool doInitialization(Module &M) override;
  bool runOnFunction(Function &F) override;
  // not overriding doFinalization

private:
  // compute the index that's log of its size based on the type that Addr
  // points to; used to index into the array based on AccessType
  int getMemoryAccessFuncIndex(Value *Addr, const DataLayout &DL); 
  // initialize OK instrumentation functions for load and store 
  void initializeLoadStoreCallbacks(Module &M);
  // initialize OK instrumentation functions for function entry and exit
  void initializeFuncCallbacks(Module &M);
  // actually insert the instrumentation call
  bool instrumentLoadOrStore(inst_iterator Iter, const DataLayout &DL);

  // Accesses sizes are powers of two in bit size: 8, 16, 32, and 64
  static const size_t kNumberOfAccessSizes = 4;
  Type *AccessType[kNumberOfAccessSizes];
  Type *AccessPtrType[kNumberOfAccessSizes];
  Function *OkBeforeRead[kNumberOfAccessSizes];
  Function *OkAfterRead[kNumberOfAccessSizes];
  Function *OkBeforeWrite[kNumberOfAccessSizes];
  Function *OkAfterWrite[kNumberOfAccessSizes];

  Function *OkFuncEntry;
  Function *OkFuncExit;

  /*
  Function *OkAfterReadFloat;
  Function *OkAfterReadDouble;
  Function *OkBeforeWriteFloat;
  Function *OkBeforeWriteDouble;
  */
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
 * void __ok_before_load<k>(void *addr, int attr);
 * void __ok_after_load<k>(void *addr, int attr, T val);
 * void __ok_before_store<k>(void *addr, int attr, T val);
 * void __ok_after_store<k>(void *addr, int attr);
 *
 * where <k> = 1, 2, 4, 8, and T is the type of the value read / written.
 * including (u)int8_t, (u)int16_t, (u)int32_t, (u)int64_t, float, and double.
 * 
 * Presumably aligned / unaligned accesses are specified by the attr
 * XXX: do we want the val to be signed or unsigned?
 * XXX: is there a separate type for unsigned int in LLVM?
 */
void OpenKimonoFunctionPass::initializeLoadStoreCallbacks(Module &M) {

  IRBuilder<> IRB(M.getContext());
  Type *RetType = IRB.getVoidTy();            // return void
  Type *AddrType = IRB.getInt8PtrTy();        // void *val
  Type *AttrType = IRB.getInt32Ty();          // int attr

  // Initialize the instrumentation for reads, writes, unaligned reads
  // unalgined writes.
  for (size_t i = 0; i < kNumberOfAccessSizes; ++i) {

    const size_t ByteSize = 1 << i;
    const size_t BitSize = ByteSize * 8;
    Type *ValType = IRB.getIntNTy(BitSize);     // uint<k>_t val
    
    AccessType[i] = ValType;
    AccessPtrType[i] = ValType->getPointerTo();

    // NOTE: nullptr is a new C++11 construct; denote a null pointer
    // here, just used to denote end of args; 
    // SmallString<32> long enough to hold 32 characters including '\0'.
    
    // void __ok_before_load<k>(void *addr, int attr);
    SmallString<32> BeforeReadName("__ok_before_load" + itostr(ByteSize));
    OkBeforeRead[i] = checkOkInterfaceFunction(
        M.getOrInsertFunction(BeforeReadName, RetType, 
                              AddrType, AttrType, nullptr)); 

    // void __ok_after_load<k>(void *addr, int attr, T val);
    SmallString<32> AfterReadName("__ok_after_load" + itostr(ByteSize));
    OkAfterRead[i] = checkOkInterfaceFunction(
        M.getOrInsertFunction(AfterReadName, RetType,
                              AddrType, AttrType, ValType, nullptr)); 

    // void __ok_before_store<k>(void *addr, int attr, T val);
    SmallString<32> BeforeWriteName("__ok_before_store" + itostr(ByteSize));
    OkBeforeWrite[i] = checkSanitizerInterfaceFunction(
        M.getOrInsertFunction(BeforeWriteName, RetType, 
                              AddrType, AttrType, ValType, nullptr));

    // void __ok_after_store<k>(void *addr, int attr);
    SmallString<32> AfterWriteName("__ok_after_store" + itostr(ByteSize));
    OkAfterWrite[i] = checkOkInterfaceFunction(
        M.getOrInsertFunction(AfterWriteName, RetType, 
                              AddrType, AttrType, nullptr)); 
  }

  // generate the type-distinct functions for float and double
  // void __ok_after_load4(void *addr, int attr, float val);
  // void __ok_after_load8(void *addr, int attr, double val);
  // void __ok_before_store4(void *addr, int attr, float val);
  // void __ok_before_store8(void *addr, int attr, float val);
  /*
  Type *FloatValType = IRB.getFloatTy();
  Type *DoubleValType = IRB.getDoubleTy();

  SmallString<32> AfterReadFloat("__ok_after_load_float");
  OkAfterReadFloat = checkOkInterfaceFunction(
      M.getOrInsertFunction(AfterReadFloat, RetType,
        AddrType, AttrType, FloatValType, nullptr)); 

  SmallString<32> AfterReadDouble("__ok_after_load_double");
  OkAfterReadDouble  = checkOkInterfaceFunction(
      M.getOrInsertFunction(AfterReadDouble, RetType,
        AddrType, AttrType, DoubleValType, nullptr)); 

  SmallString<32> BeforeWriteFloat("__ok_before_store_float");
  OkBeforeWriteFloat = checkSanitizerInterfaceFunction(
      M.getOrInsertFunction(BeforeWriteFloat, RetType, 
        AddrType, AttrType, FloatValType, nullptr));

  SmallString<32> BeforeWriteDouble("__ok_before_store_double");
  OkBeforeWriteDouble = checkSanitizerInterfaceFunction(
      M.getOrInsertFunction(BeforeWriteDouble, RetType, 
        AddrType, AttrType, DoubleValType, nullptr));
  */
}

int OpenKimonoFunctionPass::getMemoryAccessFuncIndex(Value *Addr,
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
  size_t Idx = countTrailingZeros(TypeSize / 8);
  assert(Idx < kNumberOfAccessSizes);
  return Idx;
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
  int Idx = getMemoryAccessFuncIndex(Addr, DL);
  Type *AddrType = IRB.getInt8PtrTy();

  if (Idx < 0) return false; // size that we don't recognize

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
    Function *BeforeF = OkBeforeWrite[Idx];

    /*
    if(SType == IRB.getFloatTy()) { BeforeF = OkBeforeWriteFloat; } 
    else if(SType == IRB.getDoubleTy()) { BeforeF = OkBeforeWriteDouble; }
    */

    DEBUG_WITH_TYPE("ok-func", 
        errs() << "OK_func: creating call to before store for size " 
               << Idx << " and type " << SType << "\n");
    IRB.CreateCall(BeforeF,
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(0), // XXX: use 0 for attr for now; FIXME 
         // IRB.CreateIntCast(S->getValueOperand(), AccessType[Idx])});
         S->getValueOperand()});
    // move pass the actual store instruction; 
    // the inserted instruction doesn't seem to count.
    Iter++;
    IRB.SetInsertPoint(&*Iter);

    DEBUG_WITH_TYPE("ok-func", 
        errs() << "OK_func: creating call to after store for size " 
               << Idx << "\n");
    IRB.CreateCall(OkAfterWrite[Idx],
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(0)});
    NumInstrumentedWrites++;

  } else { // is read
    LoadInst *L = cast<LoadInst>(I);
    Type *LType = L->getType();
    Function *AfterF = OkAfterRead[Idx];

    /*
    if(LType == IRB.getFloatTy()) { AfterF = OkAfterReadFloat; } 
    else if(LType == IRB.getDoubleTy()) { AfterF = OkAfterReadDouble; }
    */

    DEBUG_WITH_TYPE("ok-func", 
        errs() << "OK_func: creating call to before load for size " 
               << Idx << " and type " << LType << "\n");
    IRB.CreateCall(OkBeforeRead[Idx],
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(0)});
    // move pass the actual load instruction; 
    // the inserted instruction doesn't seem to count.
    Iter++;
    IRB.SetInsertPoint(&*Iter);

    DEBUG_WITH_TYPE("ok-func", 
        errs() << "OK_func: creating call to after load for size " 
               << Idx << "\n");
    IRB.CreateCall(AfterF,
        // XXX: should I just use the pointer type with the right size?
        {IRB.CreatePointerCast(Addr, AddrType),
         IRB.getInt32(0),
         // In LLVM, the instruction pointer represents its result
         // so we are basically passing the result of the load as 3rd arg
         // IRB.CreateIntCast(L, AccessType[Idx])});
         L});
    NumInstrumentedReads++;
  }

  return true;
}

bool OpenKimonoFunctionPass::doInitialization(Module &M) {
  DEBUG_WITH_TYPE("ok-func", errs() << "OK_func: doInitialization" << "\n");
  initializeFuncCallbacks(M);
  initializeLoadStoreCallbacks(M);
  DEBUG_WITH_TYPE("ok-func", 
      errs() << "OK_func: doInitialization done" << "\n");
  
  return true;
}

bool OpenKimonoFunctionPass::runOnFunction(Function &F) {

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

