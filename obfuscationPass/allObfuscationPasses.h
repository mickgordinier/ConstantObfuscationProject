#include <vector>         
#include <cstdint>   

#include "llvm/IR/Module.h"  
#include "llvm/IR/PassManager.h" 

using namespace llvm;

namespace {

  // struct ObfuscationPassInteger : public PassInfoMixin<ObfuscationPassInteger> {
  //   static std::vector<int> getFactors(int64_t n);

  // };

  // struct ObfuscationPassStringXOR : public PassInfoMixin<ObfuscationPassStringXOR> {
    // Hard coded key to for user to set
    // int8_t key8bit = 0x55;
    // std::set<GlobalVariable *> globalStr;
  // };

  struct ObfuscationPassStringCeasar : public PassInfoMixin<ObfuscationPassStringCeasar> {

    // Hard coded shift for user to set
    int8_t SHIFT_AMT = 5;

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  };


}