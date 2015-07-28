#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

using namespace llvm;

namespace {

  struct OpenKimono : public ModulePass {
    static char ID;
    OpenKimono() : ModulePass(ID) {}

    bool runOnModule(Module &M) override;

  private:
    void createHooks(Module &M);
    void insertFunctionHooks(Function &F);

    Module *M;
    LLVMContext *Ctx;
  }; //struct OpenKimono
} //namespace

char OpenKimono::ID = 0;
static RegisterPass<OpenKimono> X("ok", "OpenKimono instrumentation pass", false, false);

bool OpenKimono::runOnModule(Module &M) {
  // general setup
  this->M = &M;
  Ctx = &M.getContext();
  // create the functions that will need to be inserted
  createHooks();
  // go through the module and insert functions (add more calls here)
  for (Function &F : M) {
    insertFunctionHooks(F);
  }

  return true;
}

// Create all functions to insert later
void OpenKimono::createHooks() {

}

// Insert function entry and exit hooks
void OpenKimono::insertFunctionHooks(Function &F) {
}
