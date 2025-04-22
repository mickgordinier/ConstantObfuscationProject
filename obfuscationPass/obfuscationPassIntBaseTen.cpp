#include "allObfuscationPasses.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/Verifier.h"

#include <random>
#include <vector>

using namespace llvm;

// DOES NOT ENCRYPT MOST SIGNIFICANT DIGIT
// IGNORES INTEGERS THAT ARE SINGLE DIGIT (x > -10 && x < 10)

// edge cases that should be handled
//    - Most significant digit being a value that would normally map to zero
//    - Should handle negative integers
//    - Should handle changes to global variable

  // Mapping to obfuscate original integer
  std::vector<int> digits = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  llvm::GlobalVariable *constglobalArray;
  // Mapping to deobfuscate original integer
  std::vector<int> inverse = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  llvm::GlobalVariable *inverseglobalArray;

  // Takes the original integer values of the global variables and finds their obfuscated version
  // Most significant digit not obfuscated -> I.E. 100 could become 155 but the 1 remains static
  // Addresses issue where the first digit might be obfuscated to a 0 -> resulting in diff value
  static int64_t encrypt(int64_t originalValue){
    int64_t mult = 1;
    int64_t newVal = 0;
    if(originalValue < 0) {
      originalValue *= -1;
      mult = -1;
    }
    while(originalValue >= 10){
      newVal += digits[(originalValue % 10)] * mult;
      originalValue /= 10;
      mult *= 10;
    }
    newVal += (originalValue % 10) * mult;
    return newVal;
  }

  // Goes through uses of global variables and deobfuscates them before use
  // Handles stores by changing the global variable to new reobfuscated value
  static void deobfuscate(llvm::GlobalVariable &global, Function* deobfuscateFunc, Type* intTy){
    std::vector<Instruction *> globalUsers;
      for(auto U: global.users()){
        Instruction *inst = dyn_cast<Instruction>(U);
        if(!inst) continue;
        globalUsers.push_back(inst);
      }
      for(Instruction* inst: globalUsers){
        // Checks if the instruction is store requiring extra lock to ensure global variable is updated
        if (auto *store = dyn_cast<StoreInst>(inst)) {
          Value* ptrOperand = store->getPointerOperand();
          if(ptrOperand == &global){
            IRBuilder<> builder(store);
            Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr");
            Value *storeLoc = builder.CreateStore(store->getValueOperand(), ptr);
            // Reobfuscates value to store it
            Value *replacement = builder.CreateCall(deobfuscateFunc, {ptr, ptr, constglobalArray}, "reobfuscated_val");
            store->setOperand(0, replacement);
            continue;
          }
        }
        for (unsigned i = 0; i < inst->getNumOperands(); ++i) {
          if (inst->getOperand(i) == &global) {
              IRBuilder<> builder(inst);
              Value *ptr = builder.CreateAlloca(intTy, nullptr, "ptr");
              // Deobfuscates value and sets use to this new value
              Value *replacement = builder.CreateCall(deobfuscateFunc, {&global, ptr, inverseglobalArray}, "deobfuscated_val");
              inst->setOperand(i, ptr);
          }
      }
    }
  }

  static Function* insertDeobfuscateFunc(Module &M, Type* intTy) {
    LLVMContext &Ctx = M.getContext();

    PointerType* intPtrTy = PointerType::getUnqual(intTy);
    // {Pointer to globalInt, Pointer to where deobfuscatedVal should be stored, Array to use}
    // Array to use
    //    - constglobalArray: To reobfuscate
    //    - inverseglobalArray: To deobfuscate
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

    // Initializer necessary variables
    BasicBlock *entry = BasicBlock::Create(Ctx, "entry", func);
    // Check if loop should run
    BasicBlock *loopCheck = BasicBlock::Create(Ctx, "loop_check", func);
    // Looping logic
    BasicBlock *loop = BasicBlock::Create(Ctx, "loop", func);
    // Loop done and returns
    BasicBlock *exit = BasicBlock::Create(Ctx, "exit", func);
    IRBuilder<> builder(entry);

    // Loads encryptedVal and gets the absolute value for looping purposes
    Value *encryptedVal = builder.CreateLoad(intTy, encryptedValLoc, "encryptedVal");
    Value *isNegative = builder.CreateICmpSLT(encryptedVal, ConstantInt::get(intTy, 0), "isNegative");
    Value *negated = builder.CreateNeg(encryptedVal, "negatedVal");
    encryptedVal = builder.CreateSelect(isNegative, negated, encryptedVal, "absEncryptedVal");

    // Space to store output of function
    Value *result = builder.CreateAlloca(intTy, nullptr, "result");
    builder.CreateStore(ConstantInt::get(intTy, 0), result);

    // Multiplier that each digit will be multiplied by (multiplied by 10 each iteration)
    // Starts at -1 if original value was negative or 1 if original value was positive
    Value *multiplier = builder.CreateAlloca(intTy, nullptr, "multiplier");
    Value *multInit = builder.CreateSelect(
        isNegative,
        ConstantInt::get(intTy, -1),
        ConstantInt::get(intTy, 1)
    );
    builder.CreateStore(multInit, multiplier);

    // BB to check whether loop should run
    builder.CreateBr(loopCheck);
    builder.SetInsertPoint(loopCheck);

    // Value of encryptedVal at each iteration (each iteration of loop will divide it by 10)
    PHINode *phiVal = builder.CreatePHI(intTy, 2);
    phiVal->addIncoming(encryptedVal, entry);

    // Checks if encryptedVal is >= 10 at this loop iteration to see if deobfuscation should still occur
    Value *isGreaterThanTen = builder.CreateICmpSGE(phiVal, ConstantInt::get(intTy, 10));
    builder.CreateCondBr(isGreaterThanTen, loop, exit);

    builder.SetInsertPoint(loop);
    // Gets least significant digit
    Value *digit = builder.CreateURem(phiVal, ConstantInt::get(intTy, 10), "digit");

    //Gets the corresponding mapping based on the passed array (third argument)
    Value *digit32 = builder.CreateIntCast(digit, Type::getInt32Ty(Ctx), false);
    Value *gep = builder.CreateInBoundsGEP(Type::getInt8Ty(Ctx), array, digit32, "digitGEP");
    Value *mapped = builder.CreateLoad(Type::getInt8Ty(Ctx), gep, "mappedDigit");
    Value *mappedExt = builder.CreateZExt(mapped, intTy);
    // Takes the mapped digit and multiplies it by multiplier and adds it to output
    Value *mult = builder.CreateLoad(intTy, multiplier);
    Value *partial = builder.CreateMul(mappedExt, mult, "partial");
    Value *res = builder.CreateLoad(intTy, result);
    Value *updatedRes = builder.CreateAdd(res, partial);
    builder.CreateStore(updatedRes, result);

    // Handles iterations by multiplying multiplier by 10 and dividing encryptedVal by 10
    Value *newMult = builder.CreateMul(mult, ConstantInt::get(intTy, 10));
    builder.CreateStore(newMult, multiplier);
    Value *newVal = builder.CreateUDiv(phiVal, ConstantInt::get(intTy, 10));
    phiVal->addIncoming(newVal, loop);
    // Branch to loopCheck to see if loop should continue
    builder.CreateBr(loopCheck);

    builder.SetInsertPoint(exit);
    // Handles the most significant digit and adds it to the output unchanged
    digit = builder.CreateURem(phiVal, ConstantInt::get(intTy, 10), "digit");
    mult = builder.CreateLoad(intTy, multiplier);
    partial = builder.CreateMul(digit, mult, "partial");
    res = builder.CreateLoad(intTy, result);
    updatedRes = builder.CreateAdd(res, partial);
    builder.CreateStore(updatedRes, result);

    // Loads finalResult and returns value
    Value *finalRes = builder.CreateLoad(intTy, result);
    builder.CreateStore(finalRes, ptr);
    builder.CreateRet(finalRes);
    verifyFunction(*func);
    return func;
  }
  static void randomize(Module& M){
    LLVMContext &Ctx = M.getContext();
    // Shuffle order of digits/constDigit array that will be inserted into LLVM
    std::random_device rd;
    std::mt19937 g(rd());
    std::shuffle(digits.begin(), digits.end(), g);

    std::vector<llvm::Constant*> constDigits;
    for (int i = 0; i < 10; i++) {
        constDigits.push_back(llvm::ConstantInt::get(llvm::Type::getInt8Ty(Ctx), digits[i]));
        // Creates inverse mapping
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

  PreservedAnalyses obfuscationPassIntBaseTen::run(Module &M, ModuleAnalysisManager &AM) {
    // Randomize mapping and insert necessary arrays into code
    randomize(M);
    // Inserts necessary deobfuscateFunctions for each type
    Function *deobfuscateFunc8 = insertDeobfuscateFunc(M, Type::getInt8Ty(M.getContext()));
    Function *deobfuscateFunc16 = insertDeobfuscateFunc(M, Type::getInt16Ty(M.getContext()));
    Function *deobfuscateFunc32 = insertDeobfuscateFunc(M, Type::getInt32Ty(M.getContext()));
    Function *deobfuscateFunc64 = insertDeobfuscateFunc(M, Type::getInt64Ty(M.getContext()));
    for (llvm::GlobalVariable &global : M.globals()) {
      bool hasInitializer = global.hasInitializer();
      bool isIntegerType = global.getValueType()->isIntegerTy();
      bool isDefaultVisibility = global.hasDefaultVisibility();
      // Check if valid integer to obfuscate
      if (!(hasInitializer && isIntegerType && isDefaultVisibility)) {
        continue;
      }

      llvm::Type *type = global.getValueType();
      int64_t oldValue = cast<ConstantInt>(global.getInitializer())->getSExtValue();
      ConstantInt *newValue;

      // Ignore values that are single digit as we don't encrypt the most significant digit leading to no point in modifying these
      if(oldValue < 10 && oldValue > -10) continue;
      // Gets new value to set as initializer of global
      int64_t encryptedVal = encrypt(cast<ConstantInt>(global.getInitializer())->getSExtValue());
      if (type->isIntegerTy(8)) {
        newValue = llvm::ConstantInt::get(llvm::Type::getInt8Ty(global.getContext()), encryptedVal);
        // Insert deobfuscate logic for each global
        deobfuscate(global, deobfuscateFunc8, llvm::Type::getInt8Ty(global.getContext()));
      } else if (type->isIntegerTy(16)) {
        newValue = llvm::ConstantInt::get(llvm::Type::getInt16Ty(global.getContext()), encryptedVal);
        // Insert deobfuscate logic for each global
        deobfuscate(global, deobfuscateFunc16, llvm::Type::getInt16Ty(global.getContext()));
      } else if (type->isIntegerTy(32)) {
        newValue = llvm::ConstantInt::get(llvm::Type::getInt32Ty(global.getContext()), encryptedVal);
        // Insert deobfuscate logic for each global
        deobfuscate(global, deobfuscateFunc32, llvm::Type::getInt32Ty(global.getContext()));
      } else if (type->isIntegerTy(64)) {
        newValue = llvm::ConstantInt::get(llvm::Type::getInt64Ty(global.getContext()), encryptedVal);
        // Insert deobfuscate logic for each global
        deobfuscate(global, deobfuscateFunc64, llvm::Type::getInt64Ty(global.getContext()));
      } else {
        exit(1);
      }
      // Changes global initializer to newValue
      global.setInitializer(newValue);
    }
    return PreservedAnalyses::none();
  }