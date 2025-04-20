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
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"


#include <unordered_map>
#include <sstream>
#include <queue>
/* *******Implementation Ends Here******* */

#include "allObfuscationPasses.h"

// #define DEBUG

using namespace llvm;

namespace {
  struct ObfuscationPassInteger : public PassInfoMixin<ObfuscationPassInteger> {
    // template <typename T>
    // T extendKey(int8_t key, int multiple);
    // template <typename T>
    // Function* insertIntDeobfuscateFunc(Module& M, LLVMContext &C, Type* intTy, T key);
    // template<typename T>
    // void deobfuscate(llvm::GlobalVariable &global, Function* deobfuscateFunc, Type* intTy, T key);

    static std::vector<int> getFactors(int64_t n) {
      std::vector<int> factors;
      if (n < 2) return factors;
      while ((n & 1) == 0) {
          factors.push_back(2);
          n >>= 1;
      }
      for (int64_t i = 3; i * i <= n; i += 2) {
          while (n % i == 0) {
              factors.push_back(i);
              n /= i;
          }
      }
      if (n > 1) factors.push_back(n);
      return factors;
    }

    // Adds call to deobfuscation function into compiled code for undoing XOR of prime factors
    template<typename T>
    void deobfuscatePrime(llvm::GlobalVariable &globalVec, llvm::GlobalVariable &primeFactors, Function* deobfuscateFunc, Type* intTy, T key){
        std::vector<Instruction *> globalUsers;
        for(auto U: global.users()){
          Instruction *inst = dyn_cast<Instruction>(U);
          if(!inst) continue;
          globalUsers.push_back(inst);
        }
        // TODO: Check if variable updates itself -> need to set value to deobfuscated value apply change and then reobfuscate? Or some other way to keep track
        for(Instruction* inst: globalUsers){
          // if (auto *store = dyn_cast<StoreInst>(inst)) {
          //   Value* ptrOperand = store->getPointerOperand();
          //   // Handles when g is updated -> computes store and then stores reobfuscated value
          //   if(ptrOperand == &global){
          //     IRBuilder<> builder(store);
          //     Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr");
          //     Value *storeLoc = builder.CreateStore(store->getValueOperand(), ptr);
          //     Value *replacement = builder.CreateCall(deobfuscateFunc, {ptr, ptr}, "reobfuscated_val");
          //     store->setOperand(0, replacement);
          //     continue;
          //   }
          // }
          for (unsigned i = 0; i < inst->getNumOperands(); ++i) {
            if (inst->getOperand(i) == &global) {
                IRBuilder<> builder(inst);
                Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr");
                Value *replacement = builder.CreateCall(deobfuscateFuncPrime, {&primeFactors, ptr}, "deobfuscated_val");
                inst->setOperand(i, ptr);
            }
        }
      }
    }
    
    PreservedAnalyses runPrime(Module &M, ModuleAnalysisManager &AM){
      // Add deobfuscationFunction

      int totalGlobal = 0;
      int totalValidInts = 0;

      // Hard coded key for user to set
      int8_t key8Bit = 0x55;
      int32_t key32Bit = extendKey<int32_t>(key8Bit, 4);
      Function* deobfuscateFuncPrime = insertPrimeDeobfuscateFunc(M, M.getContext(), Type::getInt32Ty(M.getContext()), key32Bit);
      // Iterate through all of the global variables in the module
      for (llvm::GlobalVariable &global : M.globals()) {

        global.print(errs());
        errs() << "\n";
        
        ++totalGlobal;
        bool hasInitializer = global.hasInitializer();
        bool isIntegerType = global.getValueType()->isIntegerTy();
        bool isDefaultVisibility = global.hasDefaultVisibility();

        if (!(hasInitializer && isIntegerType && isDefaultVisibility)) {
          continue;
        }

        ++totalValidInts;
        
        int64_t originalVal = cast<ConstantInt>(global.getInitializer())->getSExtValue();
        errs() << "Initialized constant integer found with value: " << originalVal << "\n";
        llvm::Type *type = global.getValueType();
        
        // CODE FOR USING PRIME FACTORIZATION
        std::vector<int> factors = getFactors(originalVal);
        std::vector<llvm::Constant*> encryptedFactors;

        for(auto factor:factors){
          Constant* encryptedFactor = ConstantInt::get(Type::getInt32Ty(M.getContext()), factor ^ key32Bit); // TODO: Change baseed on type
          encryptedFactors.push_back(encryptedFactor);
        }

        unsigned tableSize = encryptedFactors.size(); 
        // get the element type (i32 or i64 depending on your global)
        IntegerType *elemTy = cast<IntegerType>(global.getValueType());  
        // Build an [tableSize x elemTy] array type:
        ArrayType *arrTy = ArrayType::get(elemTy, factors.size());

        Constant *arrInit = ConstantArray::get(arrTy, encryptedFactors);

        // Define global variable
        GlobalVariable *encArrGV = new GlobalVariable(
          M,                 // Module&
          arrTy,             // Type*   <-- your array type
          false,             // isConstant?
          GlobalValue::PrivateLinkage,
          arrInit,
          global.getName() + ".pf"
        );

        deobfuscatePrime(global, *encArrGV, deobfuscateFuncPrime, llvm::Type::getInt32Ty(encArrGV->getContext()), key32Bit);
      }

      errs() << "\nTotal Global Variables: " << totalGlobal;
      errs() << "\nTotal Valid Ints Variables: " << totalValidInts << "\n\n";
      
      /* *******Implementation Ends Here******* */
      // Your pass is modifying the source code. Figure out which analyses
      // are preserved and only return those, not all.
      return PreservedAnalyses::none();
    }

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
        bool hasInitializer = global.hasInitializer();
        bool isIntegerType = global.getValueType()->isIntegerTy();
        bool isDefaultVisibility = global.hasDefaultVisibility();

        if (!(hasInitializer && isIntegerType && isDefaultVisibility)) {
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
    Function* insertPrimeDeobfuscateFunc(Module &M, LLVMContext &C, Type* intTy, T key){
      PointerType* intPtrTy = PointerType::getUnqual(intTy);
      FunctionType *funcType = FunctionType::get(intTy, 
                                                 {intPtrTy, intPtrTy}, 
                                                 false);
  
      Function *func = Function::Create(funcType, 
                                        Function::ExternalLinkage, 
                                        "prime_deobf_" + std::to_string(intTy->getIntegerBitWidth()), 
                                        M);
                          
      Function::arg_iterator argsIt = func->arg_begin();
      Value *encArr = argsIt++; encArr->setName("encArr");
      Value *count  = argsIt++; count->setName("count");
      Value *outPtr = argsIt++; outPtr->setName("outPtr");

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
  };

  struct ObfuscationPassStringXOR : public PassInfoMixin<ObfuscationPassStringXOR> {
    // Hard coded key to for user to set
    int8_t key8bit = 0x55;
    std::set<GlobalVariable *> globalStr;

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
      
      // Create the string deobfuscation function for the module
      // NOT A CALL TO THE FUNCTION ITSELF
      Function* deobfuscateStringFunc = insertDeobfuscateStringFunction(M);
      
      // Iterate through all of the global variables in the module
      for (llvm::GlobalVariable &global : M.globals()) {

        // Constant variables can be ignored due to the constant folding that occurs automatically
        bool isConstant = global.isConstant();
        bool hasInitializer = global.hasInitializer();
        if(isConstant || !hasInitializer) continue;

        // Makes sure that the data type is an array as all C-strings are arrays
        if(auto *constArray = llvm::dyn_cast<llvm::ConstantDataArray>(global.getInitializer())){

          // Looking for C-strings (NOT C++ Strings) as we can determine location of \0 character
          if (!constArray->isCString()) continue;
            
          global.print(errs());
          errs() << "\n";
          
          // Get the string values
          StringRef str = constArray->getAsString();
          int strlen = str.size();
          std::string obfuscated;

          //Obfuscate the strings based on characters
          for(int i = 0; i < strlen - 1; i++){
            obfuscated.push_back(str[i] ^ key8bit);
          }

          // Reinsert null terminator at the end and converts it to llvm stsring
          auto *newArray = ConstantDataArray::getString(global.getContext(), obfuscated, true);
          newArray->print(errs());
          errs() << "\n";

          // Reassigns string to obfuscated string
          global.setInitializer(newArray);

          global.setConstant(false);
          globalStr.insert(&global);
        }
      }
      for(llvm::GlobalVariable *global: globalStr){
          // Going through each use of the string we are obfuscation
          // Allocates similar size buffer equal length inside of the main function
          // Passes the address of the allocated space to place the decrypted function
        deobfuscateString(*global, deobfuscateStringFunc);
      }
      return PreservedAnalyses::none();
    }

    // Inserting the deobfuscate function
    void deobfuscateString(llvm::GlobalVariable &global, Function* deobfuscateStringFunc){
      
      // Going through and storing all of the global variable's users
      std::vector<Instruction *> globalUsers;
      for(auto U: global.users()){
        if (Instruction *inst = dyn_cast<Instruction>(U)) {
          globalUsers.push_back(inst);
        } else if (ConstantExpr *cexpr = dyn_cast<ConstantExpr>(U)) {
          for (User *ceu : cexpr->users()) {
              if (Instruction *instUser = dyn_cast<Instruction>(ceu)) {
                  globalUsers.push_back(instUser);
              }
          }
        }
      }
      
      // Going through all of the instructions that use the obfuscated global variable value
      for(Instruction* inst: globalUsers){
        
        if (auto *store = dyn_cast<StoreInst>(inst)) {
          IRBuilder<> builder(store);
          
          // Handles when g is updated -> computes store and then stores reobfuscated value
          if(isa<Constant>(store->getValueOperand())){
            ConstantInt *encryptedChar = ConstantInt::get(Type::getInt8Ty(global.getContext()), dyn_cast<ConstantInt>(store->getValueOperand())->getZExtValue() ^ key8bit);
            store->setOperand(0, encryptedChar);
          } else{
            if (auto *load = dyn_cast<LoadInst>(store->getValueOperand())) {
              Value *loadedFrom = load->getPointerOperand();
              loadedFrom->print(errs());
              errs() << "\n";
              if (auto *ce = dyn_cast<ConstantExpr>(loadedFrom)) {
                if (ce->getOpcode() == Instruction::GetElementPtr) {
                    if (globalStr.count(dyn_cast<GlobalVariable>(ce->getOperand(0)))) {
                        continue;
                    }
                }
              }
            }
            Value* encryptedChar = builder.CreateXor(store->getValueOperand(), key8bit);
            store->setOperand(0, encryptedChar);
          }

          continue;
        }

        // Going through each operand that might contain the global variable
        // If found, creating stack space for deobfuscated value and making new call to deobfuscateValue
        for (unsigned i = 0; i < inst->getNumOperands(); ++i) {
          if (inst->getOperand(i) == &global) {
            IRBuilder<> builder(inst);
            int strlen = llvm::dyn_cast<llvm::ConstantDataArray>(global.getInitializer())->getAsString().size();
            llvm::Value *strlenValue = llvm::ConstantInt::get(llvm::Type::getInt32Ty(global.getContext()), strlen);
            Value *ptr = builder.CreateAlloca(Type::getInt8Ty(global.getContext()), strlenValue, "ptr");
            builder.CreateCall(deobfuscateStringFunc, {&global, strlenValue, ptr});
            inst->setOperand(i, ptr);
          }
        }
      }
    }

    // Create the string deobfuscation function for the module
    // NOT A CALL TO THE FUNCTION ITSELF
    Function* insertDeobfuscateStringFunction(Module &M) {
      
      LLVMContext &Ctx = M.getContext();
      llvm::PointerType* intPtr = llvm::PointerType::getUnqual(Type::getInt8Ty(Ctx));
      
      // Function type: void deobfuscate(i8*, i32)
      FunctionType *funcType = FunctionType::get(
          Type::getVoidTy(Ctx),
          {intPtr, Type::getInt32Ty(Ctx), intPtr},
          false
      );
  
      Function *func = Function::Create(
          funcType,
          Function::ExternalLinkage,
          "deobfuscate_string",
          M
      );
  
      BasicBlock *entry = BasicBlock::Create(Ctx, "entry", func);
      BasicBlock *loop = BasicBlock::Create(Ctx, "loop", func);
      BasicBlock *body = BasicBlock::Create(Ctx, "body", func);
      BasicBlock *exit = BasicBlock::Create(Ctx, "exit", func);
  
      IRBuilder<> builder(entry);
  
      auto args = func->args();
      Function::arg_iterator it = func->arg_begin();
      Value *strArg = it++;
      strArg->setName("str");
      Value *lenArg = it++;
      lenArg->setName("len");
      Value *resultPtr = it++;
      resultPtr->setName("resultPtr");
  
      Value *iAlloca = builder.CreateAlloca(Type::getInt32Ty(Ctx));
      builder.CreateStore(ConstantInt::get(Type::getInt32Ty(Ctx), 0), iAlloca);
      llvm::Value *lenMinusOne = builder.CreateSub(lenArg, llvm::ConstantInt::get(lenArg->getType(), 1), "lenMinusOne");
      builder.CreateBr(loop);
  
      builder.SetInsertPoint(loop);
      Value *iVal = builder.CreateLoad(Type::getInt32Ty(Ctx), iAlloca);
      Value *cond = builder.CreateICmpSLT(iVal, lenMinusOne);
      builder.CreateCondBr(cond, body, exit);
  
      builder.SetInsertPoint(body);
      Value *ptr = builder.CreateGEP(Type::getInt8Ty(Ctx), strArg, iVal);
      Value *c = builder.CreateLoad(Type::getInt8Ty(Ctx), ptr);
      Value *xorC = builder.CreateXor(c, ConstantInt::get(Type::getInt8Ty(Ctx), key8bit));
      Value *resultPtrElement = builder.CreateGEP(Type::getInt8Ty(Ctx), resultPtr, iVal);
      builder.CreateStore(xorC, resultPtrElement);
      Value *next = builder.CreateAdd(iVal, ConstantInt::get(Type::getInt32Ty(Ctx), 1));
      builder.CreateStore(next, iAlloca);
      builder.CreateBr(loop);
  
      builder.SetInsertPoint(exit);
      Value *lastElement = builder.CreateGEP(Type::getInt8Ty(Ctx), resultPtr, iVal);
      builder.CreateStore(ConstantInt::get(Type::getInt8Ty(Ctx), 0), lastElement);
      builder.CreateRetVoid();

      verifyFunction(*func);
      return func;
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
          if(Name == "obfuscation-int"){
            FPM.addPass(ObfuscationPassInteger());
          }
          if(Name == "obfuscation-string-xor"){
            FPM.addPass(ObfuscationPassStringXOR());
          }
          if(Name == "obfuscation-string-ceasar"){
            FPM.addPass(ObfuscationPassStringCeasar());
          }
          return true;
        }
      );
    }
  };
}
