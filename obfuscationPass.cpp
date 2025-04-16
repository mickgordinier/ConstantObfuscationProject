//===-- Frequent Path Loop Invariant Code Motion Pass --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===---------------------------------------------------------------------===//
//
// EECS583 W25 - This pass can be used as a template for your FPLICM homework
//               assignment.
//               The passes get registered as "fplicm-correctness" and
//               "fplicm-performance".
//
//
////===-------------------------------------------------------------------===//
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"

/* *******Implementation Starts Here******* */
// You can include more Header files here
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Transforms/Scalar/LoopUnrollPass.h"
#include "llvm/IR/Verifier.h"

#include <unordered_map>
#include <sstream>
#include <queue>
/* *******Implementation Ends Here******* */

// #define DEBUG

using namespace llvm;

namespace {

  template <typename T>
  T extendKey(int8_t key, int multiple);
  Function* insertDeobfuscate(Module& M, LLVMContext &C, int32_t key);


  struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
      // llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      // llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      // llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);

      /* *******Implementation Starts Here******* */
      // Your core logic should reside here.

      // Add deobfuscationFunction

      int totalGlobal = 0;
      int totalValidInts = 0;

      // Hard coded key for user to set
      int8_t key8Bit = 0x55;

      int16_t key16Bit = extendKey<int16_t>(key8Bit, 2);
      int32_t key32Bit = extendKey<int32_t>(key8Bit, 4);
      int64_t key64Bit = extendKey<int64_t>(key8Bit, 8);

      Function* deobfuscateFunc = insertDeobfuscate(M, M.getContext(), key32Bit);

      // Iterate through all of the global variables in the module
      for (llvm::GlobalVariable &global : M.globals()) {
        global.print(errs());
        errs() << "\n";
        
        ++totalGlobal;
        
        bool isConstant = global.isConstant();
        isConstant = true;
        bool hasInitializer = global.hasInitializer();
        bool isIntegerType = global.getValueType()->isIntegerTy();
        bool isDefaultVisibility = global.hasDefaultVisibility();
        
        if (!(isConstant && 
          hasInitializer && 
          isIntegerType && 
              isDefaultVisibility)) {
          continue;
        }

        ++totalValidInts;
        
        int64_t originalVal = cast<ConstantInt>(global.getInitializer())->getSExtValue();
          
        errs() << "Initialized constant integer found with value: " << originalVal << "\n";

        llvm::Type *type = global.getValueType();

        ConstantInt *newValue;

        if (type->isIntegerTy(8)) {
          int8_t encryptedVal = originalVal ^ key8Bit;
          newValue = llvm::ConstantInt::get(llvm::Type::getInt8Ty(global.getContext()), encryptedVal);
        } else if (type->isIntegerTy(16)) {
          int16_t encryptedVal = originalVal ^ key16Bit;
          newValue = llvm::ConstantInt::get(llvm::Type::getInt16Ty(global.getContext()), encryptedVal);
        } else if (type->isIntegerTy(32)) {
          int32_t encryptedVal = originalVal ^ key32Bit;
          newValue = llvm::ConstantInt::get(llvm::Type::getInt32Ty(global.getContext()), encryptedVal);
        } else if (type->isIntegerTy(64)) {
          int64_t encryptedVal = originalVal ^ key64Bit;
          newValue = llvm::ConstantInt::get(llvm::Type::getInt64Ty(global.getContext()), encryptedVal);
        } else {
          exit(1);
        }

        global.setInitializer(newValue);
        errs() << "Modified global variable: " << global.getName() << ", New Value: " 
       << cast<ConstantInt>(global
        .getInitializer())->getSExtValue() << "\n";



        // result = result ^= hardCodedKeyExtended;
        // errs() << "DECRYPTED RESULT: " << result << "\n\n";
        // Go through uses
        std::vector<Instruction *> globalUsers;
        for(auto U: global.users()){
          Instruction *inst = dyn_cast<Instruction>(U);
          if(!inst) continue;
          globalUsers.push_back(inst);
        }
        for(Instruction* inst: globalUsers){
          for (unsigned i = 0; i < inst->getNumOperands(); ++i) {
            if (inst->getOperand(i) == &global) {

                IRBuilder<> builder(inst);
                Value *ptr = builder.CreateAlloca(Type::getInt32Ty(M.getContext()), nullptr, "ptr");
                Value *replacement = builder.CreateCall(deobfuscateFunc, {&global, ptr}, "transformed");
                inst->print(errs());
                errs() << "\n";
                inst->setOperand(i, ptr);
                inst->print(errs());
                errs() << "\n";
            }
        }
        }
      }

      errs() << "\nTotal Global Variables: " << totalGlobal;
      errs() << "\nTotal Valid Ints Variables: " << totalValidInts << "\n\n";

      
      
      /* *******Implementation Ends Here******* */
      // Your pass is modifying the source code. Figure out which analyses
      // are preserved and only return those, not all.
      return PreservedAnalyses::none();
    }
  };

  template <typename T>
  T extendKey(int8_t key, int multiple) {

    T extendedKey;

    int i;
    for (i = 0; i < multiple; ++i) {
      extendedKey <<= 8;
      extendedKey |= key;
    }
    return extendedKey;
  }
  Function* insertDeobfuscate(Module &M, LLVMContext &C, int32_t key){
    FunctionType *funcType = FunctionType::get(Type::getInt32Ty(C), 
                                               {PointerType::getUnqual(Type::getInt32Ty(C)), PointerType::getUnqual(Type::getInt32Ty(C))}, 
                                               false);

    Function *func = Function::Create(funcType, 
                                      Function::ExternalLinkage, 
                                      "deobfuscate", 
                                      M);
    Function::arg_iterator args = func->arg_begin();
    Value *encryptedValLoc = args++;
    encryptedValLoc->setName("encryptedValLoc");
    Value *ptr = args++;
    ptr->setName("ptr");

    BasicBlock *entry = BasicBlock::Create(C, "entry", func);
    IRBuilder<> builder(entry);

    // Example: return a + b;
    Value *encryptedVal = builder.CreateLoad(Type::getInt32Ty(C), encryptedValLoc, "encryptedVal");
    Value *result = builder.CreateXor(encryptedVal, key, "result");
    Value *resultLoc = builder.CreateStore(result, ptr);
    builder.CreateRet(result);

    verifyFunction(*func);

    return func;
  };
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, ModulePassManager &FPM,
        ArrayRef<PassBuilder::PipelineElement>) {
            FPM.addPass(HW2CorrectnessPass());
          // if(Name == "fplicm-performance"){
          //   FPM.addPass(HW2PerformancePass());
          //   return true;
          // }
          return true;
        }
      );
    }
  };
}
