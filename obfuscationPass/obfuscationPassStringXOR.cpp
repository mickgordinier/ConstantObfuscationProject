#include "allObfuscationPasses.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/Verifier.h"

using namespace llvm;

  
  // Inserting the deobfuscate function
  static void 
  deobfuscateString(
    llvm::GlobalVariable &global, 
    Function* deobfuscateStringFunc,
    int8_t key8bit,
    std::set<GlobalVariable *> &globalStr
  )
  {
    
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
  static Function* 
  insertDeobfuscateStringFunction(Module &M, int8_t key8bit) {
      
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

  PreservedAnalyses 
  ObfuscationPassStringXOR::run(
    Module &M, 
    ModuleAnalysisManager &AM) 
  {
    
    // Create the string deobfuscation function for the module
    // NOT A CALL TO THE FUNCTION ITSELF
    Function* deobfuscateStringFunc = insertDeobfuscateStringFunction(M, key8bit);
    
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
      deobfuscateString(*global, deobfuscateStringFunc, key8bit, globalStr);
    }
    return PreservedAnalyses::none();
  }