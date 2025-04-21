#include "allObfuscationPasses.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/Verifier.h"

#include <random>
#include <vector>

using namespace llvm;

namespace {
  struct obfuscationPassIntBaseTen : public PassInfoMixin<obfuscationPassIntBaseTen> {

    std::vector<int> digits = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    std::vector<int> inverse = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    llvm::GlobalVariable *constglobalArray;
    llvm::GlobalVariable *inverseglobalArray;

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
      randomize(M);
      Function *deobfuscateFunc8 = insertDeobfuscateFunc(M, Type::getInt8Ty(M.getContext()));
      Function *deobfuscateFunc16 = insertDeobfuscateFunc(M, Type::getInt16Ty(M.getContext()));
      Function *deobfuscateFunc32 = insertDeobfuscateFunc(M, Type::getInt32Ty(M.getContext()));
      Function *deobfuscateFunc64 = insertDeobfuscateFunc(M, Type::getInt64Ty(M.getContext()));
      for (llvm::GlobalVariable &global : M.globals()) {
        bool hasInitializer = global.hasInitializer();
        bool isIntegerType = global.getValueType()->isIntegerTy();
        bool isDefaultVisibility = global.hasDefaultVisibility();

        if (!(hasInitializer && isIntegerType && isDefaultVisibility)) {
          continue;
        }

        llvm::Type *type = global.getValueType();
        ConstantInt *newValue;

        int64_t encryptedVal = encrypt(cast<ConstantInt>(global.getInitializer())->getSExtValue());
        if (type->isIntegerTy(8)) {
          newValue = llvm::ConstantInt::get(llvm::Type::getInt8Ty(global.getContext()), encryptedVal);
          deobfuscate(global, deobfuscateFunc8, llvm::Type::getInt8Ty(global.getContext()));
        } else if (type->isIntegerTy(16)) {
          newValue = llvm::ConstantInt::get(llvm::Type::getInt16Ty(global.getContext()), encryptedVal);
          deobfuscate(global, deobfuscateFunc16, llvm::Type::getInt16Ty(global.getContext()));
        } else if (type->isIntegerTy(32)) {
          newValue = llvm::ConstantInt::get(llvm::Type::getInt32Ty(global.getContext()), encryptedVal);
          deobfuscate(global, deobfuscateFunc32, llvm::Type::getInt32Ty(global.getContext()));
        } else if (type->isIntegerTy(64)) {
          newValue = llvm::ConstantInt::get(llvm::Type::getInt64Ty(global.getContext()), encryptedVal);
          deobfuscate(global, deobfuscateFunc64, llvm::Type::getInt64Ty(global.getContext()));
        } else {
          exit(1);
        }
        global.setInitializer(newValue);
      }
      return PreservedAnalyses::none();
    }
    int64_t encrypt(int64_t originalValue){
      int64_t newVal = 0;
      int64_t mult = 1;
      while(originalValue != 0){
        newVal += digits[(originalValue % 10)] * mult;
        originalValue /= 10;
        mult *= 10;
      }
      return newVal;
    }

    void deobfuscate(llvm::GlobalVariable &global, Function* deobfuscateFunc, Type* intTy){
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
              Value *replacement = builder.CreateCall(deobfuscateFunc, {ptr, ptr, constglobalArray}, "reobfuscated_val");
              store->setOperand(0, replacement);
              continue;
            }
          }
          for (unsigned i = 0; i < inst->getNumOperands(); ++i) {
            if (inst->getOperand(i) == &global) {
                IRBuilder<> builder(inst);
                Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr");
                Value *replacement = builder.CreateCall(deobfuscateFunc, {&global, ptr, inverseglobalArray}, "deobfuscated_val");
                inst->setOperand(i, ptr);
            }
        }
      }
    }

    Function* insertDeobfuscateFunc(Module &M, Type* intTy) {
      LLVMContext &Ctx = M.getContext();

      PointerType* intPtrTy = PointerType::getUnqual(intTy);
      FunctionType *funcType = FunctionType::get(intTy, 
                                                 {intPtrTy, intPtrTy, PointerType::getUnqual(Type::getInt8Ty(Ctx))}, 
                                                 false);
  
      Function *func = Function::Create(funcType, 
                                        Function::ExternalLinkage, 
                                        "deobfuscateBaseFunc"  + std::to_string(intTy->getIntegerBitWidth()), 
                                        M);
      Function::arg_iterator args = func->arg_begin();
      Value *encryptedValLoc = args++;
      encryptedValLoc->setName("encryptedValLoc");
      Value *ptr = args++;
      ptr->setName("ptr");
      Value *array = args++;
      array->setName("array");

      BasicBlock *entry = BasicBlock::Create(Ctx, "entry", func);
      BasicBlock *loopCheck = BasicBlock::Create(Ctx, "loop_check", func);
      BasicBlock *loop = BasicBlock::Create(Ctx, "loop", func);
      BasicBlock *exit = BasicBlock::Create(Ctx, "exit", func);
      IRBuilder<> builder(entry);
      Value *encryptedVal = builder.CreateLoad(intTy, encryptedValLoc, "encryptedVal");
      Value *result = builder.CreateAlloca(intTy, nullptr, "result");
      builder.CreateStore(ConstantInt::get(intTy, 0), result);

      Value *multiplier = builder.CreateAlloca(intTy, nullptr, "multiplier");
      builder.CreateStore(ConstantInt::get(intTy, 1), multiplier);

      builder.CreateBr(loopCheck);
      builder.SetInsertPoint(loopCheck);
      PHINode *phiVal = builder.CreatePHI(intTy, 2);
      phiVal->addIncoming(encryptedVal, entry);

      Value *isZero = builder.CreateICmpEQ(phiVal, ConstantInt::get(intTy, 0));
      builder.CreateCondBr(isZero, exit, loop);

      builder.SetInsertPoint(loop);
      Value *digit = builder.CreateURem(phiVal, ConstantInt::get(intTy, 10), "digit");
      Value *digit32 = builder.CreateIntCast(digit, Type::getInt32Ty(Ctx), false);
      Value *gep = builder.CreateInBoundsGEP(Type::getInt8Ty(Ctx), array, digit32, "digitGEP");
      Value *mapped = builder.CreateLoad(Type::getInt8Ty(Ctx), gep, "mappedDigit");
      Value *mappedExt = builder.CreateZExt(mapped, intTy);
      Value *mult = builder.CreateLoad(intTy, multiplier);
      Value *partial = builder.CreateMul(mappedExt, mult, "partial");
      Value *res = builder.CreateLoad(intTy, result);
      Value *updatedRes = builder.CreateAdd(res, partial);
      builder.CreateStore(updatedRes, result);

      Value *newMult = builder.CreateMul(mult, ConstantInt::get(intTy, 10));
      builder.CreateStore(newMult, multiplier);

      Value *newVal = builder.CreateUDiv(phiVal, ConstantInt::get(intTy, 10));
      phiVal->addIncoming(newVal, loop);
      builder.CreateBr(loopCheck);

      builder.SetInsertPoint(exit);
      Value *finalRes = builder.CreateLoad(intTy, result);
      builder.CreateStore(finalRes, ptr);
      builder.CreateRet(finalRes);
      verifyFunction(*func);
      return func;
    }
    void randomize(Module& M){
      LLVMContext &Ctx = M.getContext();
      // Shuffle order of digits/constDigit array that will be inserted into LLVM
      std::random_device rd;
      std::mt19937 g(rd());
      std::shuffle(digits.begin(), digits.end(), g);

      std::vector<llvm::Constant*> constDigits;
      for (int i = 0; i < 10; i++) {
          constDigits.push_back(llvm::ConstantInt::get(llvm::Type::getInt8Ty(Ctx), digits[i]));
          inverse[digits[i]] = i;
      }
      std::vector<llvm::Constant*> inverseDigits;
      for (int i = 0; i < 10; i++) {
        inverseDigits.push_back(llvm::ConstantInt::get(llvm::Type::getInt8Ty(Ctx), inverse[i]));
    }

      // Create an LLVM constant array of those digits
      llvm::ArrayType *arrayType = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), digits.size());
      llvm::Constant *constArray = llvm::ConstantArray::get(arrayType, constDigits);
      // Insert constant array into llvm
      constglobalArray = new llvm::GlobalVariable(
        M,
        arrayType,
        true,
        llvm::GlobalValue::ExternalLinkage,
        constArray,
        "constDigits"
      );
      llvm::Constant *inverseArray = llvm::ConstantArray::get(arrayType, inverseDigits);
      // Insert inverse array into llvm
      inverseglobalArray = new llvm::GlobalVariable(
        M,
        arrayType,
        true,
        llvm::GlobalValue::ExternalLinkage,
        inverseArray,
        "inverseDigits"
      );
    }
  };
}
