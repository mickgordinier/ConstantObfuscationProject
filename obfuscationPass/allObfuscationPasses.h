#include <vector>         
#include <cstdint>   
#include <set>

#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/Verifier.h"

using namespace llvm;

  struct ObfuscationPassStringXOR : public PassInfoMixin<ObfuscationPassStringXOR> {
    // Hard coded key to for user to set
    int8_t key8bit = 0x55;
    std::set<GlobalVariable *> globalStr;

    llvm::PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  };

  struct ObfuscationPassStringCeasar : public PassInfoMixin<ObfuscationPassStringCeasar> {
    
    // Hard coded shift for user to set
    int8_t SHIFT_AMT = 5;
    std::set<GlobalVariable *> globalStr;
    
    llvm::PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  };

  struct obfuscationPassIntBaseTen : public PassInfoMixin<obfuscationPassIntBaseTen> {
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  };
  struct obfuscationPassPrime : public PassInfoMixin<obfuscationPassIntBaseTen> {
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  };
