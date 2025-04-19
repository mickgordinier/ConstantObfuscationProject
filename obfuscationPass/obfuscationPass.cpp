//===-- Frequent Path Loop Invariant Code Motion Pass --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===---------------------------------------------------------------------===//
//
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
  template <typename T>
  Function* insertIntDeobfuscateFunc(Module& M, LLVMContext &C, Type* intTy, T key);
  template<typename T>
  void deobfuscate(llvm::GlobalVariable &global, Function* deobfuscateFunc, Type* intTy, T key);


  struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {

      // Add deobfuscationFunction

      int totalGlobal = 0;
      int totalValidInts = 0;

      // Hard coded key for user to set
      int8_t key8Bit = 0x55;

      int16_t key16Bit = extendKey<int16_t>(key8Bit, 2);
      int32_t key32Bit = extendKey<int32_t>(key8Bit, 4);
      int64_t key64Bit = extendKey<int64_t>(key8Bit, 8);

      Function* deobfuscateFunc8 = insertIntDeobfuscateFunc(M, M.getContext(), Type::getInt8Ty(M.getContext()), key8Bit);
      Function* deobfuscateFunc16 = insertIntDeobfuscateFunc(M, M.getContext(), Type::getInt16Ty(M.getContext()), key16Bit);
      Function* deobfuscateFunc32 = insertIntDeobfuscateFunc(M, M.getContext(), Type::getInt32Ty(M.getContext()), key32Bit);
      Function* deobfuscateFunc64 = insertIntDeobfuscateFunc(M, M.getContext(), Type::getInt64Ty(M.getContext()), key64Bit);

      // Iterate through all of the global variables in the module
      for (llvm::GlobalVariable &global : M.globals()) {
        global.print(errs());
        errs() << "\n";
        
        ++totalGlobal;
        
        bool isConstant = global.isConstant();
        isConstant = true; // clang optimizes const values out so doesn't work.
        bool hasInitializer = global.hasInitializer();
        bool isIntegerType = global.getValueType()->isIntegerTy();
        bool isDefaultVisibility = global.hasDefaultVisibility();
        if(auto *constArray = llvm::dyn_cast<llvm::ConstantDataArray>(global.getInitializer())){
          if (constArray->isString()){
            //Finds strings
          }
        }
        
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
          deobfuscate(global, deobfuscateFunc8, llvm::Type::getInt8Ty(global.getContext()), key8Bit);
        } else if (type->isIntegerTy(16)) {
          int16_t encryptedVal = originalVal ^ key16Bit;
          newValue = llvm::ConstantInt::get(llvm::Type::getInt16Ty(global.getContext()), encryptedVal);
          deobfuscate(global, deobfuscateFunc16, llvm::Type::getInt16Ty(global.getContext()), key16Bit);
        } else if (type->isIntegerTy(32)) {
          int32_t encryptedVal = originalVal ^ key32Bit;
          newValue = llvm::ConstantInt::get(llvm::Type::getInt32Ty(global.getContext()), encryptedVal);
          deobfuscate(global, deobfuscateFunc32, llvm::Type::getInt32Ty(global.getContext()), key32Bit);
        } else if (type->isIntegerTy(64)) {
          int64_t encryptedVal = originalVal ^ key64Bit;
          newValue = llvm::ConstantInt::get(llvm::Type::getInt64Ty(global.getContext()), encryptedVal);
          deobfuscate(global, deobfuscateFunc64, llvm::Type::getInt64Ty(global.getContext()), key64Bit);
        } else {
          exit(1);
        }

        global.setInitializer(newValue);
        errs() << "Modified global variable: " << global.getName() << ", New Value: " 
       << cast<ConstantInt>(global
        .getInitializer())->getSExtValue() << "\n";
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
  // Inserts deobfuscation function into compiled code for undoing XOR of ints against hard-coded value
  template<typename T>
  Function* insertIntDeobfuscateFunc(Module &M, LLVMContext &C, Type* intTy, T key){
    PointerType* intPtrTy = PointerType::getUnqual(intTy);
    FunctionType *funcType = FunctionType::get(intTy, 
                                               {intPtrTy, intPtrTy}, 
                                               false);

    Function *func = Function::Create(funcType, 
                                      Function::ExternalLinkage, 
                                      "deobfuscate_" + std::to_string(intTy->getIntegerBitWidth()), 
                                      M);
    Function::arg_iterator args = func->arg_begin();
    Value *encryptedValLoc = args++;
    encryptedValLoc->setName("encryptedValLoc");
    Value *ptr = args++;
    ptr->setName("ptr");

    BasicBlock *entry = BasicBlock::Create(C, "entry", func);
    IRBuilder<> builder(entry);

    // Example: return a + b;
    Value *encryptedVal = builder.CreateLoad(intTy, encryptedValLoc, "encryptedVal");
    Value *result = builder.CreateXor(encryptedVal, key, "result");
    Value *resultLoc = builder.CreateStore(result, ptr);
    builder.CreateRet(result);

    verifyFunction(*func);

    return func;
  };
  // Adds call to deobfuscation function into compiled code for undoing XOR of ints against hard-coded value
  template<typename T>
  void deobfuscate(llvm::GlobalVariable &global, Function* deobfuscateFunc, Type* intTy, T key){
      std::vector<Instruction *> globalUsers;
      for(auto U: global.users()){
        Instruction *inst = dyn_cast<Instruction>(U);
        if(!inst) continue;
        globalUsers.push_back(inst);
      }
      // TODO: Check if variable updates itself -> need to set value to deobfuscated value apply change and then reobfuscate? Or some other way to keep track
      for(Instruction* inst: globalUsers){
        if (auto *store = dyn_cast<StoreInst>(inst)) {
          Value* ptrOperand = store->getPointerOperand();
          // Handles when g is updated -> computes store and then stores reobfuscated value
          if(ptrOperand == &global){
            IRBuilder<> builder(store);
            Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr");
            Value *storeLoc = builder.CreateStore(store->getValueOperand(), ptr);
            Value *replacement = builder.CreateCall(deobfuscateFunc, {ptr, ptr}, "reobfuscated_val");
            store->setOperand(0, replacement);
            continue;
          }
        }
        for (unsigned i = 0; i < inst->getNumOperands(); ++i) {
          if (inst->getOperand(i) == &global) {
              IRBuilder<> builder(inst);
              Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr");
              Value *replacement = builder.CreateCall(deobfuscateFunc, {&global, ptr}, "deobfuscated_val");
              inst->setOperand(i, ptr);
          }
      }
    }
  };
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, ModulePassManager &FPM,
        ArrayRef<PassBuilder::PipelineElement>) {
          if(Name == "obfuscation-global"){
            FPM.addPass(HW2CorrectnessPass());
          }
          return true;
        }
      );
    }
  };
}
