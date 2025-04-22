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
// #include "obfuscationPassIntBaseTen.cpp"

#include <unordered_map>
#include <sstream>
#include <queue>
/* *******Implementation Ends Here******* */

#include "allObfuscationPasses.h"

// #define DEBUG

using namespace llvm;



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
    void deobfuscatePrime(Module &M, llvm::GlobalVariable &global, llvm::GlobalVariable &primeFactors, Value* count, Function* deobfuscateFunc, Type* intTy, T key){
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
                Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr"); //
                builder.CreateCall(deobfuscateFunc, {&primeFactors, count, ptr}, "deobfuscated_val");
                inst->setOperand(i, ptr);
            }
        }
      }
    }
    // Inserts deobfuscation function into compiled code for undoing XOR of ints against hard-coded value
    template<typename T>
    Function* insertPrimeDeobfuscateFunc(Module &M, LLVMContext &C, Type* intTy, T key){
      LLVMContext &Ctx = M.getContext();

      auto *i32Ty  = Type::getInt32Ty(Ctx);
      PointerType* intPtrTy = PointerType::getUnqual(intTy);
      FunctionType *funcType = FunctionType::get(intTy, 
                                                 {intPtrTy, i32Ty, intPtrTy}, 
                                                 false);
  
      Function *func = Function::Create(funcType, 
                                        Function::ExternalLinkage, 
                                        "prime_deobf_" + std::to_string(intTy->getIntegerBitWidth()), 
                                        M);

      // Create the BBs for the entire function body
      BasicBlock *loopPreheader = BasicBlock::Create(Ctx, "loopPreheader", func);
      BasicBlock *loopHeader = BasicBlock::Create(Ctx, "loopHeader", func); 
      BasicBlock *loopBody = BasicBlock::Create(Ctx, "loopBody", func);
      BasicBlock *loopExit = BasicBlock::Create(Ctx, "loopExit", func);
                              
      Function::arg_iterator argsIt = func->arg_begin();
      Value *encArr = argsIt++; encArr->setName("encArr");
      errs() << "enc arr read\n";
      Value *count  = argsIt++; count->setName("count");
      errs() << "count read\n";
      Value *outPtr = argsIt++; outPtr->setName("outPtr");
      errs() << "outPtr read\n";

      // Creating the instructions for the function body, with BB "loopPreheader" as entry point
      IRBuilder<> builder(loopPreheader);
  
      // Placing instructions at loopPreheader BB
      // Creates i32 on the stack and initializes it to 0 (For currentIdx)
      // Unconditionally branches to loopHeader BB
      Value *iAlloca = builder.CreateAlloca(Type::getInt32Ty(Ctx));
      builder.CreateStore(ConstantInt::get(Type::getInt32Ty(Ctx), 0), iAlloca);
      builder.CreateStore(ConstantInt::get(Type::getInt32Ty(Ctx), 1), outPtr);
      builder.CreateBr(loopHeader);
  
      // Starts inserting all new instructions in loopHeader BB
      builder.SetInsertPoint(loopHeader);
      Value *currentIdx = builder.CreateLoad(Type::getInt32Ty(Ctx), iAlloca);                    // currentIdx = iAlloca
      Value *cond = builder.CreateICmpSLT(currentIdx, count);                              // cond = currentIdx < count
      builder.CreateCondBr(cond, loopBody, loopExit);                                            // br (cond) loopBody loopEdit

      // Starts inserting all new instructions in loopBody BB
      builder.SetInsertPoint(loopBody);
      Value *ptr = builder.CreateGEP(Type::getInt32Ty(Ctx), encArr, currentIdx);                  // ptr = &encArr[currentIdx]
      Value *ct = builder.CreateLoad(Type::getInt32Ty(Ctx), ptr);                                 // ct = *ptr
      Value *decryptedFactor = builder.CreateXor(ct, key, "decFactor");                           // decFactor = ct XOR
    
      Value* result = builder.CreateLoad(Type::getInt32Ty(Ctx), outPtr);
      Value* product = builder.CreateMul(result, decryptedFactor, "mulRes");
      builder.CreateStore(product, outPtr);

      Value *next = builder.CreateAdd(currentIdx, ConstantInt::get(Type::getInt32Ty(Ctx), 1));   // currentIdx++
      builder.CreateStore(next, iAlloca);                                                        // iAlloca = currentIdx
      builder.CreateBr(loopHeader);                                                              // b loopHeader
  
      // Starts inserting all new instructions in loopExit BB
      builder.SetInsertPoint(loopExit);

      builder.CreateRet(ConstantInt::get(Type::getInt32Ty(Ctx), 1));                                                                   // reutrn void
      
      verifyFunction(*func);
  
      return func;
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
    PreservedAnalyses obfuscationPassPrime::run(Module &M, ModuleAnalysisManager &AM){
      // Add deobfuscationFunction

      int totalGlobal = 0;
      int totalValidInts = 0;

      // Hard coded key for user to set
      int8_t key8Bit = 0x55;
      int32_t key32Bit = extendKey<int32_t>(key8Bit, 4);
      std::vector<llvm::GlobalVariable*> deletedGlobals{};
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
        IntegerType *elemTy = Type::getInt32Ty(M.getContext());//cast<IntegerType>(global.getValueType());  
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
        llvm::Value* sizeValue = llvm::ConstantInt::get(llvm::Type::getInt32Ty(M.getContext()), tableSize);
        Function* deobfuscateFuncPrime = insertPrimeDeobfuscateFunc(M, M.getContext(), Type::getInt32Ty(M.getContext()), key32Bit); //TODO: change arguments
        deobfuscatePrime(M, global, *encArrGV, sizeValue, deobfuscateFuncPrime,  llvm::Type::getInt32Ty(encArrGV->getContext()), key32Bit);
        deletedGlobals.push_back(&global);
        
      }
      // DELETING
      for(llvm::GlobalVariable * global: deletedGlobals){
        global->eraseFromParent();
      }
      errs() << "\nTotal Global Variables: " << totalGlobal;
      errs() << "\nTotal Valid Ints Variables: " << totalValidInts << "\n\n";
      
      /* *******Implementation Ends Here******* */
      // Your pass is modifying the source code. Figure out which analyses
      // are preserved and only return those, not all.
      return PreservedAnalyses::none();
    }

