#include "allObfuscationPasses.h"

#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/Verifier.h"

using namespace llvm;

namespace {
  
  // Inserting the deobfuscate function
  static void 
  deobfuscateStringCeasar(llvm::GlobalVariable &global, Function* deobfuscateStringFunc, int8_t SHIFT_AMT){
  
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
          ConstantInt *encryptedChar = ConstantInt::get(Type::getInt8Ty(global.getContext()), dyn_cast<ConstantInt>(store->getValueOperand())->getZExtValue() + SHIFT_AMT);
          store->setOperand(0, encryptedChar);
        } else{
          llvm::Value *val = llvm::ConstantInt::get(llvm::Type::getInt8Ty(global.getContext()), SHIFT_AMT);
          Value* encryptedChar = builder.CreateAdd(store->getValueOperand(), val);
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
  static Function* 
  insertDeobfuscateStringCeasarFunction(Module &M, int8_t SHIFT_AMT) {
    
    LLVMContext &Ctx = M.getContext();
  
    // Creating an i8* pointer type
    llvm::PointerType* intPtr = llvm::PointerType::getUnqual(Type::getInt8Ty(Ctx));
    
    // Function type: void deobfuscate(i8*, i32, i8*)
    // i8* - Pointer to the current obfuscated string buffer
    // i32 - Length of string
    // i8* - Pointer to the buffer where we want to store the deobfuscated value
    FunctionType *funcType = FunctionType::get(
        Type::getVoidTy(Ctx),
        {intPtr, Type::getInt32Ty(Ctx), intPtr},
        false
    );
  
    // Creating the function decleration for the ceasar deobfuscation
    Function *func = Function::Create(
        funcType,                         // Passing the return and parameter types
        Function::ExternalLinkage,
        "deobfuscate_string_ceasar",      // Name of the function
        M                                 // Module function will be located in
    );
  
    // Create the BBs for the entire function body
    BasicBlock *loopPreheader = BasicBlock::Create(Ctx, "loopPreheader", func);
    BasicBlock *loopHeader = BasicBlock::Create(Ctx, "loopHeader", func); 
    BasicBlock *loopBody = BasicBlock::Create(Ctx, "loopBody", func);
    BasicBlock *loopExit = BasicBlock::Create(Ctx, "loopExit", func);
  
    // Obtaining the value for all the arguments
    Function::arg_iterator it = func->arg_begin();
    Value *strArg = it++;
    strArg->setName("str");
    Value *lenArg = it++;
    lenArg->setName("len");
    Value *resultPtr = it++;
    resultPtr->setName("resultPtr");
    
    // Creating the instructions for the function body, with BB "loopPreheader" as entry point
    IRBuilder<> builder(loopPreheader);
  
    // Placing instructions at loopPreheader BB
    // Creates i32 on the stack and initializes it to 0 (For currentIdx)
    // Creates value %lenMinusOne = sub i32 %len, 1     (Want len-1 because we want to ignore null char)
    // Unconditionally branches to loopHeader BB
    Value *iAlloca = builder.CreateAlloca(Type::getInt32Ty(Ctx));
    builder.CreateStore(ConstantInt::get(Type::getInt32Ty(Ctx), 0), iAlloca);
    llvm::Value *lenMinusOne = builder.CreateSub(lenArg, llvm::ConstantInt::get(lenArg->getType(), 1), "lenMinusOne");
    builder.CreateBr(loopHeader);
  
    // Starts inserting all new instructions in loopHeader BB
    builder.SetInsertPoint(loopHeader);
    Value *currentIdx = builder.CreateLoad(Type::getInt32Ty(Ctx), iAlloca);                    // currentIdx = iAlloca
    Value *cond = builder.CreateICmpSLT(currentIdx, lenMinusOne);                              // cond = currentIdx < lenMinusOne
    builder.CreateCondBr(cond, loopBody, loopExit);                                            // br (cond) loopBody loopEdit
  
    // Starts inserting all new instructions in loopBody BB
    builder.SetInsertPoint(loopBody);
    Value *ptr = builder.CreateGEP(Type::getInt8Ty(Ctx), strArg, currentIdx);                  // ptr = &strArg[currentIdx]
    Value *ct = builder.CreateLoad(Type::getInt8Ty(Ctx), ptr);                                 // ct = *ptr
    Value *pt = builder.CreateSub(ct, ConstantInt::get(Type::getInt8Ty(Ctx), SHIFT_AMT));      // pt = ct - SHIFT_AMT
    Value *resultPtrElement = builder.CreateGEP(Type::getInt8Ty(Ctx), resultPtr, currentIdx);  // resultPtrElement = &resultPtr[currentIdx]
    builder.CreateStore(pt, resultPtrElement);                                                 // *resultPtrElement = pt
    Value *next = builder.CreateAdd(currentIdx, ConstantInt::get(Type::getInt32Ty(Ctx), 1));   // currentIdx++
    builder.CreateStore(next, iAlloca);                                                        // iAlloca = currentIdx
    builder.CreateBr(loopHeader);                                                              // b loopHeader
  
    // Starts inserting all new instructions in loopExit BB
    builder.SetInsertPoint(loopExit);
    Value *lastElement = builder.CreateGEP(Type::getInt8Ty(Ctx), resultPtr, currentIdx);       // lastElement = &resultPtr[lenMinusOne]
    builder.CreateStore(ConstantInt::get(Type::getInt8Ty(Ctx), 0), lastElement);               // *lastElement = '\0'
    builder.CreateRetVoid();                                                                   // reutrn void
  
    verifyFunction(*func);
    return func;
  }

  PreservedAnalyses 
  ObfuscationPassStringCeasar::run(Module &M, ModuleAnalysisManager &AM) {
    
    // Create the string deobfuscation ceasar function for the module
    // NOT A CALL TO THE FUNCTION ITSELF
    Function* deobfuscateStringFunc = insertDeobfuscateStringCeasarFunction(M, SHIFT_AMT);
    
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
          obfuscated.push_back(str[i] + SHIFT_AMT);
        }

        // Reinsert null terminator at the end and converts it to llvm stsring
        auto *newArray = ConstantDataArray::getString(global.getContext(), obfuscated, true);
        newArray->print(errs());
        errs() << "\n";

        // Reassigns string to obfuscated string
        global.setInitializer(newArray);

        global.setConstant(false);

        // Going through each use of the string we are obfuscation
        // Allocates similar size buffer equal length inside of the main function
        // Passes the address of the allocated space to place the decrypted function
        deobfuscateStringCeasar(global, deobfuscateStringFunc, SHIFT_AMT);
      }
    }
    return PreservedAnalyses::none();
  }
};