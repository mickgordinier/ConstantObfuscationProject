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

#include <unordered_map>
#include <sstream>
#include <queue>
/* *******Implementation Ends Here******* */

// #define DEBUG

using namespace llvm;

namespace {

  // struct OLDhoistInstructionInfo {
  //   Instruction* I;
  //   SSAUpdater* ownSSAUpdater;
  //   SSAUpdater* dependentSSAUpdater;
  //   bool isOriginalLoad;
  //   int operandIdxUpdating = -1;
  // };

  
  struct hoistInstructionInfo {
    Instruction* I;
    Instruction* clonedDependentPreheader;
    std::unordered_map<BasicBlock*, Instruction*> clonedDependentInfrequentInstructions;
    bool isOriginalLoad;
    int operandIdxUpdating = -1;
  };
  
  void 
  prefixLoop(
    llvm::BranchProbabilityAnalysis::Result &bpi,
    llvm::LoopAnalysis::Result &li,
    Loop* loop_info,
    std::unordered_map<BasicBlock*, bool> &blocksInLoop,
    std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads,
    BasicBlock* &PreHeaderBlock
  );

  void 
  almostLoopInvariantCodeMotion(
    Function &F,
    llvm::LoopAnalysis::Result &li,
    llvm::BranchProbabilityAnalysis::Result &bpi
  );

  void 
  removeRedundantLoadsWithinLoop(
    Function &F);

  void 
  deadCodeElimination(
    Function &F);

  void
  createBlocksInLoopList(
    const llvm::BranchProbabilityAnalysis::Result &bpi,
    const llvm::LoopAnalysis::Result &li,
    const Loop *loop_info,
    BasicBlock* &PreHeaderBlock,
    std::unordered_map<BasicBlock*, bool> &blocksInLoop
  );

  void
  printBasicBlocksInLoop(
    std::unordered_map<BasicBlock*, bool> &blocksInLoop
  );

  void
  searchForInvariantLoads(
    std::unordered_map<BasicBlock*, bool> &blocksInLoop,
    std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads
  );

  void
  printInvariantLoadList(
    std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads
  );

  void
  performLoadHoisting(
    BasicBlock* &PreHeaderBlock,
    const std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads
  );

  void
  performAdvancedLoadArithmeticHoisting(
    Loop *loop_info,
    BasicBlock* &PreHeaderBlock,
    const std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads,
    int loopIdx
  );

  Instruction*
  cloneInstructionToPreheader(
    BasicBlock* PreHeaderBlock,
    Instruction* instructionToHoist,
    Value* valueForOperandToLookAt,
    int operandIdxToUpdate,
    bool isOriginalLoad
  );

  std::vector<llvm::Instruction*>
  cloneInstructionAfterInfrequentStore(
    std::set<llvm::Instruction *> &associatedInfrequentStoreInstructions,
    Instruction* instructionToHoist,
    std::unordered_map<llvm::BasicBlock*, llvm::Instruction*> &infrequentClonedInstructions,
    int operandIdxToUpdate,
    bool isOriginalLoad
  );

  void
  updateDependentInstructions(
    Loop *loop_info,
    Instruction* instructionHoisting,
    Instruction* clonedPreheaderInstruction,
    std::vector<llvm::Instruction*>& clonedInfrequentInstructions,
    std::queue<hoistInstructionInfo>& hoistedInstructionQueue,
    const std::string &loadUpdaterNodeName,
    int &hoistInstructionIdx
  );

  // void
  // OLDperformAdvancedLoadArithmeticHoisting(
  //   Loop *loop_info,
  //   BasicBlock* &PreHeaderBlock,
  //   const std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads,
  //   int loopIdx
  // );

  // void
  // OLDcloneInstructionToPreheader(
  //   BasicBlock* PreHeaderBlock,
  //   hoistInstructionInfo &hoistInstruction
  // );

  // void
  // OLDcloneInstructionAfterInfrequentStore(
  //   std::set<llvm::Instruction *> &associatedInfrequentStoreInstructions,
  //   hoistInstructionInfo &hoistInstruction
  // );

  // void
  // OLDupdateDependentInstructions(
  //   Loop *loop_info,
  //   hoistInstructionInfo &hoistInstruction,
  //   std::queue<hoistInstructionInfo> &hoistedInstructionQueue,
  //   const std::string &loadUpdaterNodeName,
  //   int &hoistInstructionIdx
  // );

  template <typename T>
  T extendKey(int8_t key, int multiple);


  struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
      // llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      // llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      // llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);

      /* *******Implementation Starts Here******* */
      // Your core logic should reside here.

      int totalGlobal = 0;
      int totalValidInts = 0;

      // Hard coded key for user to set
      int8_t key8Bit = 0x55;

      int16_t key16Bit = extendKey<int16_t>(key8Bit, 2);
      int32_t key32Bit = extendKey<int32_t>(key8Bit, 4);
      int64_t key64Bit = extendKey<int64_t>(key8Bit, 8);

      // Iterate through all of the global variables in the module
      for (llvm::GlobalVariable &global : M.globals()) {
        
        ++totalGlobal;
        
        bool isConstant = global.isConstant();
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



        // result = result ^= hardCodedKeyExtended;
        // errs() << "DECRYPTED RESULT: " << result << "\n\n";












        // errs() << "\n";
        // errs() << "Get Initializer: " << cast<ConstantInt>(global.getInitializer())->getSExtValue() << "\n";
        // // getIntegerValue(global.getType(), global);
        
        // // Printing out basic info of global variable
        // errs() << "Is Constant: " << global.isConstant() << "\n";
        // errs() << "Is isExternallyInitialized: " << global.isExternallyInitialized() << "\n";
        // errs() << "Is hasUniqueInitializer: " << global.hasUniqueInitializer() << "\n";
        // errs() << "Is hasDefinitiveInitializer: " << global.hasDefinitiveInitializer() << "\n";
        // errs() << "Is hasInitializer: " << global.hasInitializer() << "\n";
        // errs() << "Is getSection: " << global.getSection() << "\n";
        // errs() << "Is getTypeEnum: " << global.getType()->getTypeID() << "\n";
        // errs() << "Is getTypePrint: ";
        // global.getType()->print(errs()); 
        // errs() << "\n";
        // errs() << "Is getValueType: " << global.getValueType()->isIntegerTy() << "\n";
        // errs() << "Is getValueTypePrint: ";
        // // global.getValueType()->getTypeID().print(errs()); 
        // errs() << "\n";
        // errs() << "Value of Global Variable: ";
        // global.print(errs());
        // errs() << "\n";
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


  void prefixLoop(
    llvm::BranchProbabilityAnalysis::Result &bpi,
    llvm::LoopAnalysis::Result &li,
    Loop* loop_info,
    std::unordered_map<BasicBlock*, bool> &blocksInLoop,
    std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads,
    BasicBlock* &PreHeaderBlock)
  {
    // 1. Finding all the basic blocks in the loop's frequent path

    // Fills in blocksInLoop, indicating the BB in this specific loop
    // Also indicates twhat the PreHeaderBasicBlock is
    createBlocksInLoopList(bpi, li, loop_info, PreHeaderBlock, blocksInLoop);

    // Optional Print
    // printBasicBlocksInLoop(blocksInLoop);


    // 2. Find the invariant loads instructions
    searchForInvariantLoads(blocksInLoop, invariantLoads);
    
    // Optional Print
    // printInvariantLoadList(invariantLoads);
  }


  void almostLoopInvariantCodeMotion(
    Function &F,
    llvm::LoopAnalysis::Result &li,
    llvm::BranchProbabilityAnalysis::Result &bpi
  )
  {

    int loopIdx = 0;

    // Performing Almost Invariant Load Hoisting for each loop individually
    for (Loop * loop_info : li) {

      // Set to keep track of all the basic blocks that exist in the loop
      // Bool value to indicate if basic block is in the frequent path
      // Assume each frequent edge has AT LEAST a probability of 0.8
      std::unordered_map<BasicBlock*, bool> blocksInLoop;
      
      BasicBlock *PreHeaderBlock;

      // Will contain list of invariant loads that can be hoisted
      // It's value contains the set of associated infrequent store instructions
      std::unordered_map<Instruction*, std::set<Instruction*>> invariantLoads;

      prefixLoop(bpi, li, loop_info, blocksInLoop, invariantLoads, PreHeaderBlock);

      // Perform Almost Invariant Load-Hoisting
      // Also fixes up all infrequent store instructions
      // ALSO BUMPS UP ALL ARTIHMETIC INSTRUCTIONS THAT CAN BE HOISTED IN LOOP
      performAdvancedLoadArithmeticHoisting(loop_info, PreHeaderBlock, invariantLoads, loopIdx);

      ++loopIdx;
    }
  }


  void removeRedundantLoadsWithinLoop(
    Function &F)
  {
    for (BasicBlock& BB : F) {
        
      for (Instruction& I : BB) {

        if (std::string(I.getOpcodeName()) == "load") {

          bool canSafelyMerge = true;
          std::vector<llvm::Instruction*> instructionsToMerge;

          Value* operandValue = I.getOperand(0);

          // Going through all uses of the given pointer operand
          for (auto U : operandValue->users()) { // U is of type User *
            
            // If the user is an instruction
            if (auto otherI = dyn_cast<Instruction>(U)) {

              if (otherI->getParent() != I.getParent()) continue;

              // Cannot safely merge load instructions with a store inside the BB
              if (std::string(otherI->getOpcodeName()) == "store") {
                canSafelyMerge = false;
                break;
              }

              if (I.isIdenticalTo(otherI) && (otherI != &I)) {
                instructionsToMerge.push_back(otherI);
              }
            }
          }

          if (!canSafelyMerge) continue;
          if (instructionsToMerge.empty()) continue;

          // errs() << "FOUND LOADS TO MERGE ON BASIC BLOCK: ";
          // I.getParent()->printAsOperand(errs());
          // errs() << "\n";

          // errs() << "Main Instruction: " << I << "\n";

          for (Instruction* otherI : instructionsToMerge) {
            // errs() << "Duplicated in-block Instruction: " << *otherI << "\n";
          }
          // errs() << "\n\n";

          // Going through all the duplicated instructions, repointing definitions, and erasing duplicates
          for (Instruction* instructionMerging : instructionsToMerge) {
            
            // Going through all uses of the given pointer operand
            for (auto U : instructionMerging->users()) { // U is of type User *
              
              // If the user is an instruction
              if (auto dependentInstruction = dyn_cast<Instruction>(U)) {

                int operandIdxToUpdate = -1;

                for (int operandIdx = 0; operandIdx < dependentInstruction->getNumOperands(); ++operandIdx) {
                  if (dependentInstruction->getOperand(operandIdx) == instructionMerging) {
                    dependentInstruction->setOperand(operandIdx, &I);
                    break;
                  }
                }

              }
            }

            instructionMerging->eraseFromParent();
          }

        }
      }
    }
  }


  void deadCodeElimination(
    Function &F)
  {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {

      if ((I->getNumUses() == 0) &&
      (std::string(I->getOpcodeName()) != "store") &&
      (std::string(I->getOpcodeName()) != "br") &&
      (std::string(I->getOpcodeName()) != "call") &&
      (std::string(I->getOpcodeName()) != "ret")) {
        errs() << "DEAD CODE FOUND!!!\n";
        errs() << "Instruction Type: " << I->getOpcodeName() << "\n";
        errs() << "Basic Block Location: ";
        I->getParent()->printAsOperand(errs());
        errs() << "\n" << *I << "\n\n";
      }
    }
  }


  void printBasicBlockInstructions(
    std::string title,
    BasicBlock* BB) 
  {
    errs() << "\n-----------------------------------------------\n";
    errs() << title << "\n";
    errs() << "-----------------------------------------------\n";
    for (Instruction& I : *BB) {
      errs() << I << "\n";
    }
    errs() << "-----------------------------------------------\n";
  }

  void
  createBlocksInLoopList(
    const llvm::BranchProbabilityAnalysis::Result &bpi,
    const llvm::LoopAnalysis::Result &li,
    const Loop *loop_info,
    BasicBlock* &PreHeaderBlock,
    std::unordered_map<BasicBlock*, bool> &blocksInLoop)
  {

    #ifdef DEBUG
      errs() << "\n=== FINDING FREQUENT PATH ===\n\n";
    #endif

    PreHeaderBlock = loop_info->getLoopPreheader();

    #ifdef DEBUG
      errs() << "Loop enters on Basic Block ";
      PreHeaderBlock->printAsOperand(errs(), false);
    
      errs() << "\n\n";
    #endif

    // We assume that there exist only one exit from the Loop Pre-header
    // That successor will be the Loop Header (The Conditional)
    BasicBlock *HeaderBlock = *succ_begin(PreHeaderBlock);

    // The HeaderBlock is in the loop and is part of the frequent path
    blocksInLoop.insert({HeaderBlock, true});

    // Need to go through all of the infrequent basic blocks
    // Need to know all blocks that exist WITHIN the loop,
    std::deque<BasicBlock*> blocksToCheck;

    blocksToCheck.push_back(HeaderBlock);

    // Iterating through the basic blocks found in the most frequent path
    // Next iteration will be the next BB on the frequent path
    // Starting at Loop Header (Not Pre-Header)
    while (!blocksToCheck.empty()) {

      BasicBlock* TopBlock = blocksToCheck.front();
      blocksToCheck.pop_front();

      // Finding the successor Basic Blocks within loop
      Instruction* terminator_inst = TopBlock->getTerminator();

      if (terminator_inst->getOpcode() == Instruction::Br) {
      
        for (unsigned i = 0; i < terminator_inst->getNumSuccessors(); ++i) {

          BasicBlock *Succ = terminator_inst->getSuccessor(i);
          
          if (blocksInLoop.find(Succ) != blocksInLoop.end()) {
            continue;
          }

          // If the node is an exit, it is not part of the loop
          // TODO: THIS IS NOT A PROPER WAY OF LOOP DETECTION
          // TODO: IF MULTIPLE LOOPS, THIS CAN BE A PROBLEM
          if (li.getLoopDepth(Succ) == 0) {
            continue;
          }
          
          blocksToCheck.push_back(Succ);

          BranchProbability Prob = bpi.getEdgeProbability(TopBlock, Succ);
          double prob_double = (double) Prob.getNumerator() / (double) Prob.getDenominator();
          
          // If sucessor block is frequent
          bool isFrequent = prob_double >= 0.79;
          blocksInLoop.insert({Succ, isFrequent});
        }
      }
    }
  }


  void
  printBasicBlocksInLoop(
    std::unordered_map<BasicBlock*, bool> &blocksInLoop)
  {
    errs() << "-----------------------------------------------\n";
    errs() << "List of Basic Blocks In Loop\n";
    errs() << "-----------------------------------------------\n";
    for (auto bbIter : blocksInLoop) {
      
      bbIter.first->printAsOperand(errs());

      if (bbIter.second) {
        errs() << " (IN FREQUENT PATH)";
      }
      errs()<< "\n";
    }
    errs() << "-----------------------------------------------\n\n";
  }


  void
  searchForInvariantLoads(
    std::unordered_map<BasicBlock*, bool> &blocksInLoop,
    std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads)
  {

    #ifdef DEBUG
      errs() << "\n=== SEARCHING FOR INVARIANT INSTRUCTIONS ===\n\n";
    #endif

    // Going through each basic block in the most frequent path
    for (auto bbIter : blocksInLoop) {

      if (bbIter.second == false) {
        continue;
      }

      BasicBlock *BB = bbIter.first;

      // Going through the instructions within the basic block
      // Looking for loads and stores
      for (Instruction &I : *BB) {

        if (std::string(I.getOpcodeName()) == "load") {

          std::set<Instruction*> infreqentStores;

          Value* operandValue = I.getOperand(0);

          #ifdef DEBUG
            errs() << I << " (";
            operandValue->printAsOperand(errs());
            errs() << ")\n";
          #endif

          // We are looking for loads that are dependent ONLY on infreqent stores
          // If there is a store within the frequent path --> NO hoisting
          bool onlyInfrequentStores = true;
          bool anyInfrequentStores = false;

          // Going through all uses of the given pointer operand
          for (auto U : operandValue->users()) { // U is of type User *
            
            // If the user is an instruction
            if (auto otherI = dyn_cast<Instruction>(U)) {

              if (std::string(otherI->getOpcodeName()) == "store") {

                #ifdef DEBUG
                  errs() << "(OTHER USES) " << *otherI;
                #endif

                if ((blocksInLoop.find(otherI->getParent()) != blocksInLoop.end())) {

                  if (blocksInLoop[otherI->getParent()]) {
                    #ifdef DEBUG
                      errs() << " (IN FREQUENT PATH)\n";
                    #endif
                    onlyInfrequentStores = false;
                    break;
                  } else {
                    #ifdef DEBUG
                      errs() << " (NOT IN FREQUENT PATH)\n";
                    #endif
                    anyInfrequentStores = true;
                    infreqentStores.insert(otherI);
                  }

                }
              }
            }
          }

          if (onlyInfrequentStores && anyInfrequentStores) {
            #ifdef DEBUG
              errs() << "LOAD IS INVARIANT!!\n";
            #endif
            invariantLoads.insert({&I, infreqentStores});
          } else {
            #ifdef DEBUG
              errs() << "Load is not invariant\n";
            #endif
          }

          #ifdef DEBUG
            errs() << "\n";
          #endif
        }
      }
    }
    
    #ifdef DEBUG
      errs() << "\n";
    #endif
  }


  void
  printInvariantLoadList(
    std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads
  )
  {
    errs() << "-----------------------------------------------\n";
    errs() << "List of Invariant Load Instructions\n";
    errs() << "-----------------------------------------------\n";
    for (auto invariantLoadIter : invariantLoads) {

      Instruction *invariantLoad = invariantLoadIter.first;

      errs() << *invariantLoad << "    (BB ";
      invariantLoad->getParent()->printAsOperand(errs());
      errs() << ")\n";

      for (auto infrequentStoreIter : invariantLoadIter.second) {
        errs() << "  " << *infrequentStoreIter << "    (BB ";
        infrequentStoreIter->getParent()->printAsOperand(errs());
        errs() << ")\n";
      }

      errs() << "\n";
    }
    errs() << "-----------------------------------------------\n\n";
  }


  void
  performLoadHoisting(
    BasicBlock* &PreHeaderBlock,
    const std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads
  )
  {

    #ifdef DEBUG
      errs() << "\n=== PERFORMING LOAD HOISTING OF INVARIANTS ===\n\n";
    #endif

    std::string phiNodeName = "inv_var";
    int phiNodeIdx = 0;

    for (auto invariantLoadIter : invariantLoads) {
      
      // For each of the detected almost invariant loads
      Instruction *invariantLoad = invariantLoadIter.first;
      
      #ifdef DEBUG
        errs() << "\nFixing up almost invariant load: " << *invariantLoad << "\n";
      #endif
      
      // Keeping track of all the re-definitions of the Value Pointer
      Value *ptrValue = invariantLoad->getOperand(0);

      llvm::SSAUpdater updater;
      updater.Initialize(invariantLoad->getType(), phiNodeName + std::to_string(phiNodeIdx));

      // i. Hoist load to the pre-header
      //    Placing clone of load instruction at the end of pre-header (Before the terminator)
      #ifdef DEBUG
        errs() << "Cloning load instruction to end of Pre-Header\n";
      #endif

      // printBasicBlockInstructions("ORIGINAL PREHEADER", PreHeaderBlock);
      
      Instruction* cloneInstForPreHeader = invariantLoad->clone();
      cloneInstForPreHeader->insertBefore(PreHeaderBlock->getTerminator());

      // printBasicBlockInstructions("AFTER LOAD INSERTION PREHEADER", PreHeaderBlock);

      updater.AddAvailableValue(PreHeaderBlock, cloneInstForPreHeader);

      #ifdef DEBUG
        errs() << "\n[BEGIN] ADDING LOADS AT INFREQUENT BLOCKS WITH STORE\n\n";
      #endif

      // ii. Recompute load at the infrequent blocks that the stores occur
      for (auto infrequentStoreIter : invariantLoadIter.second) {

        BasicBlock *InfrequentBlockWithStore = infrequentStoreIter->getParent();

        #ifdef DEBUG
          errs() << "Cloning load instruction after infrequent store block ";
          InfrequentBlockWithStore->printAsOperand(errs());
          errs() << "\n";
          
          printBasicBlockInstructions("ORIGINAL INFREQUENT BLOCK", InfrequentBlockWithStore);
        #endif

        Instruction* cloneInstForInfrequentBlock = invariantLoad->clone();
        cloneInstForInfrequentBlock->insertBefore(InfrequentBlockWithStore->getTerminator());

        #ifdef DEBUG
          printBasicBlockInstructions("INFREQUENT BLOCK AFTER LOAD INSERTION", InfrequentBlockWithStore);
        #endif

        updater.AddAvailableValue(InfrequentBlockWithStore, cloneInstForInfrequentBlock);
      }

      #ifdef DEBUG
        errs() << "\n[END] ADDING LOADS AT INFREQUENT BLOCKS WITH STORE\n";
      #endif


      // iii. Need to update all instructions that used original load instruction
      //      Need to loop at phi node now
      
      #ifdef DEBUG
        errs() << "\n[BEGIN] UPDATE NEED TO ADD PHI NODES TO ACCOUNT FOR NEW LOADS\n";
      #endif

      for (auto U : invariantLoad->users()) { // U is of type User *
        if (auto otherI = dyn_cast<Instruction>(U)) {

          #ifdef DEBUG
            errs() << "\n(OTHER USES) " << *otherI << "\n";
          #endif
          
          if (std::string(otherI->getOpcodeName()) == "phi") {
            #ifdef DEBUG
              errs() << "PHI NODE DETECTED, SKIPPING\n";
            #endif

            continue;
          }

          #ifdef DEBUG
            printBasicBlockInstructions("ORIGINAL USE OF ORGINAL LOAD", otherI->getParent());
          #endif

          updater.RewriteUse(U->getOperandUse(0));
          
          #ifdef DEBUG
            printBasicBlockInstructions("UPDATED VALUE AFTER ACCOUNTING FOR PHI NODE", otherI->getParent());
          #endif
        }
      }

      invariantLoad->eraseFromParent();    
      
    }
  }


  void
  performAdvancedLoadArithmeticHoisting(
    Loop *loop_info,
    BasicBlock* &PreHeaderBlock,
    const std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads,
    int loopIdx
  )
  {
    #ifdef DEBUG
      errs() << "\n=== PERFORMING LOAD HOISTING OF INVARIANTS + ADVANCED!! ===\n\n";
    #endif

    int loadInstructionIdx = 0;
    
    std::string updaterNodeName = "hoist(" + std::to_string(loopIdx) + ")";
    
    for (auto invariantLoadIter : invariantLoads) {

      // Will be continiously hoisting up as many instructions as we can
      // We start by hoisting the almost invariant load
      // Need to fix up by add instruction after infrequent store and using SSAUpdater 

      std::string loadUpdaterNodeName = updaterNodeName + "(" + std::to_string(loadInstructionIdx) + ")";

      std::queue<hoistInstructionInfo> hoistedInstructionQueue;
      
      std::unordered_map<BasicBlock*, Instruction*> temp;
      hoistedInstructionQueue.push({invariantLoadIter.first, nullptr, temp, true, -1});

      int hoistInstructionIdx = 1;

      while (!hoistedInstructionQueue.empty()) {

        hoistInstructionInfo hoistInstruction = hoistedInstructionQueue.front();

        #ifdef DEBUG
          errs() << "\nHOSTING NEW INSTRUCTION: " << *hoistInstruction.I;
          errs() << "\nLOCATED IN BASIC BLOCK: ";
          hoistInstruction.I->getParent()->printAsOperand(errs()); 
          errs() << "\n";
        #endif

        // i. Hoist instruction to the end of the pre-header
        //    Placing clone of load instruction at the end of pre-header (Before the terminator)
        //    Will update SSAUpdater to indicate new value calcualted in PreHeader
        Instruction* preHeaderClonedInstruction = cloneInstructionToPreheader(
                                                    PreHeaderBlock, 
                                                    hoistInstruction.I,
                                                    hoistInstruction.clonedDependentPreheader,
                                                    hoistInstruction.operandIdxUpdating,
                                                    hoistInstruction.isOriginalLoad
                                                  );


        // ii. Recompute instruction at the infrequent blocks that the stores occur
        //     Places instruction at end of BB with infrequent store for recomputation
        //     Will update SSAUpdater to indicate new value calcualted in each BB it is placed in
        std::vector<llvm::Instruction*> clonedInfrequentStores = cloneInstructionAfterInfrequentStore(
                                                                  invariantLoadIter.second, 
                                                                  hoistInstruction.I,
                                                                  hoistInstruction.clonedDependentInfrequentInstructions,
                                                                  hoistInstruction.operandIdxUpdating,
                                                                  hoistInstruction.isOriginalLoad
                                                                );


        // iii. Need to update all instructions that used original load instruction
        //      instructionSSAUpdater now contains all proper redeclerations of returned value
        //      All instructions dependent on original instruction now need to look at instructionSSAUpdater value
        //      Will also determine if instruction can now also be hoisted (Within loop and is now truly LICM)
        updateDependentInstructions(
          loop_info,
          hoistInstruction.I,
          preHeaderClonedInstruction,
          clonedInfrequentStores,
          hoistedInstructionQueue,
          loadUpdaterNodeName, 
          hoistInstructionIdx
        );


        // iv. Now all depend instructions looking at SSAUpdater Value instead
        //     Instruction has been properly hoisted and we can now safely delete original instruction
        
        #ifdef DEBUG
          errs() << "ERASING INSTRUCTION SAFELY\n";
        #endif

        hoistInstruction.I->eraseFromParent();    

        // delete instructionSSAUpdater;
        hoistedInstructionQueue.pop();

      }

      ++loadInstructionIdx;
    }
  }
  
  
  Instruction*
  cloneInstructionToPreheader(
    BasicBlock* PreHeaderBlock,
    Instruction* instructionToHoist,
    Value* valueForOperandToLookAt,
    int operandIdxToUpdate,
    bool isOriginalLoad
  )
  {
    #ifdef DEBUG
      errs() << "\n[BEGIN] ADD INSTRUCTION AT END OF PREHEADER\n\n";
      printBasicBlockInstructions("ORIGINAL PREHEADER", PreHeaderBlock);
    #endif


    Instruction* clonedInstForPreHeader = instructionToHoist->clone();
    clonedInstForPreHeader->insertBefore(PreHeaderBlock->getTerminator());

    // Updating dependent instruction to look at specific instruction value
    if (!isOriginalLoad) {
      clonedInstForPreHeader->setOperand(operandIdxToUpdate, valueForOperandToLookAt);
    }

    #ifdef DEBUG
      printBasicBlockInstructions("AFTER LOAD INSERTION PREHEADER", PreHeaderBlock);
      errs() << "\n[END] ADD INSTRUCTION AT END OF PREHEADER\n\n";
    #endif
    
    // Need to keep track of where all instructions are located
    return clonedInstForPreHeader;
  }
  
  
  std::vector<llvm::Instruction*>
  cloneInstructionAfterInfrequentStore(
    std::set<llvm::Instruction *> &associatedInfrequentStoreInstructions,
    Instruction* instructionToHoist,
    std::unordered_map<llvm::BasicBlock*, llvm::Instruction*> &infrequentClonedInstructions,
    int operandIdxToUpdate,
    bool isOriginalLoad
  )
  {
    #ifdef DEBUG
    // errs() << "\n[BEGIN] ADDING INSTRUCTION AT INFREQUENT BLOCKS WITH STORE\n\n";
    #endif

    std::vector<llvm::Instruction*> clonedInfrequentInstructions;

    for (auto infrequentStoreIter : associatedInfrequentStoreInstructions) {

      BasicBlock *InfrequentBlockWithStore = infrequentStoreIter->getParent();

      #ifdef DEBUG
        errs() << "Cloning load instruction after infrequent store block ";
        InfrequentBlockWithStore->printAsOperand(errs());
        errs() << "\n";
        
        printBasicBlockInstructions("ORIGINAL INFREQUENT BLOCK", InfrequentBlockWithStore);
      #endif

      Instruction* cloneInstForInfrequentBlock = instructionToHoist->clone();
      cloneInstForInfrequentBlock->insertBefore(InfrequentBlockWithStore->getTerminator());

      if (!isOriginalLoad) {
        Value* valueForOperandToLookAt = infrequentClonedInstructions[InfrequentBlockWithStore];
        cloneInstForInfrequentBlock->setOperand(operandIdxToUpdate, valueForOperandToLookAt);
      }

      clonedInfrequentInstructions.push_back(cloneInstForInfrequentBlock);

      #ifdef DEBUG
        printBasicBlockInstructions("INFREQUENT BLOCK AFTER LOAD INSERTION", InfrequentBlockWithStore);
      #endif
    }

    #ifdef DEBUG
      errs() << "\n[END] ADDING LOADS AT INFREQUENT BLOCKS WITH STORE\n";
    #endif

    return clonedInfrequentInstructions;
  }
  
  
  void
  updateDependentInstructions(
    Loop *loop_info,
    Instruction* instructionHoisting,
    Instruction* clonedPreheaderInstruction,
    std::vector<llvm::Instruction*>& clonedInfrequentInstructions,
    std::queue<hoistInstructionInfo>& hoistedInstructionQueue,
    const std::string &loadUpdaterNodeName,
    int &hoistInstructionIdx
  )
  {
    #ifdef DEBUG
      errs() << "\n[BEGIN] UPDATE ALL DEPENDENT INSTRUCTION TO LOOK AT SSAUPDATER\n";
    #endif

    std::vector<std::pair<llvm::Instruction*, int>> nonInvariantInstructionPostHoist;

    // Going through all instructions that depend on hoisted instruction
    for (auto U : instructionHoisting->users()) { // U is of type User *
      if (auto otherI = dyn_cast<Instruction>(U)) {  // Recasting as instruction

        #ifdef DEBUG
          errs() << "\n(DEPENDENT INSTRUCTION) " << *otherI << "\n";
          errs() << "Located at Basic Block: ";
          otherI->getParent()->printAsOperand(errs());
          errs() << "\n\n";
        #endif
        
        if (std::string(otherI->getOpcodeName()) == "phi") {
          #ifdef DEBUG
            errs() << "PHI NODE DETECTED, SKIPPING\n";
          #endif

          continue;
        }

        int operandIdxToUpdate = -1;

        for (int operandIdx = 0; operandIdx < otherI->getNumOperands(); ++operandIdx) {
          if (otherI->getOperand(operandIdx) == instructionHoisting) {
            operandIdxToUpdate = operandIdx;
            break;
          }
        }

        if (operandIdxToUpdate == -1) {
          errs() << "OPERAND TO UPDATE NOT FOUND\n";
          exit(1);
        }
        
        // NOW, determining if instruction is hoistable (ALL its other operands are loop invariant)
        // If they are, we do not need an SSAUpdater assignment for the current instruction we are hoisting
        // If there exist 1 instruction that is still not invariant, need to create SSA updater for current instruction

        // Going through each operand to determine if instruction is same to hoist
        bool safeToHoist = true;

        // If the dependent instruction is not in the same basic block, will not hoist
        // Will also need to create SSA Updater for this instruction
        if (otherI->getParent() != instructionHoisting->getParent()) {
          safeToHoist = false;
        };

        for (int operandIdx = 0; operandIdx < otherI->getNumOperands(); ++operandIdx) {

          // The phi node update is not loop invariant
          if (operandIdx == operandIdxToUpdate) continue;
          
          Value* operandValue = otherI->getOperand(operandIdx);

          #ifdef DEBUG
            errs() << "OPERAND VALUE: ";
            operandValue->printAsOperand(errs());
            errs() << "\n";
          #endif

          if (!loop_info->isLoopInvariant(operandValue)) {
            safeToHoist = false;
            break;
          }
        }

        if (safeToHoist) {
          
          // No need to create SSA UPDATER for this instruction
          // Will loop directly at Preheader and cloned instructions

          hoistInstructionInfo newHoistInstruction;

          newHoistInstruction.I = otherI;
          newHoistInstruction.isOriginalLoad = false;
          newHoistInstruction.operandIdxUpdating = operandIdxToUpdate;

          newHoistInstruction.clonedDependentPreheader = clonedPreheaderInstruction;

          for (Instruction* clonedDependentInfrequent : clonedInfrequentInstructions) {
            newHoistInstruction.clonedDependentInfrequentInstructions[clonedDependentInfrequent->getParent()] = clonedDependentInfrequent;
          }

          hoistedInstructionQueue.push(newHoistInstruction);

        } else {
          nonInvariantInstructionPostHoist.push_back({otherI, operandIdxToUpdate});
        }
      
      }
    }


    // If there exist any instructions that remain non-Invariant post hoisting
    // We need to create an SSA Updater for the instruction we are hoisting and perform re-assignment
    if (!nonInvariantInstructionPostHoist.empty()) {
      
      // Creating SSA Updater for this instruction
      // Adding uses anytime instruction is cloned
      llvm::SSAUpdater* newSSAUpdater = new llvm::SSAUpdater();
      std::string updaterNodeName = loadUpdaterNodeName + "(" + std::to_string(hoistInstructionIdx++) + ")";

      newSSAUpdater->Initialize(instructionHoisting->getType(), updaterNodeName);

      newSSAUpdater->AddAvailableValue(clonedPreheaderInstruction->getParent(), clonedPreheaderInstruction);

      for (Instruction* clonedInstruction : clonedInfrequentInstructions) {
        newSSAUpdater->AddAvailableValue(clonedInstruction->getParent(), clonedInstruction);
      }

      // Updating each of the usage of operand
      for (size_t i = 0; i < nonInvariantInstructionPostHoist.size(); ++i) {
        Instruction* nonInvariantInstruction = nonInvariantInstructionPostHoist[i].first;
        int operandIdxToUpdate = nonInvariantInstructionPostHoist[i].second;

        newSSAUpdater->RewriteUse(dyn_cast<llvm::User>(nonInvariantInstruction)->getOperandUse(operandIdxToUpdate));
      }
    }
   
   #ifdef DEBUG
     errs() << "\n[END] UPDATE DEPENDENT INSTRUCTION TO LOOK AT SSAUPDATER\n";
   #endif 
  }
  
  
  

  // void
  // OLDperformAdvancedLoadArithmeticHoisting(
  //   Loop *loop_info,
  //   BasicBlock* &PreHeaderBlock,
  //   const std::unordered_map<Instruction*, std::set<Instruction*>> &invariantLoads,
  //   int loopIdx
  // )
  // {
  //   // #ifdef DEBUG
  //     errs() << "\n=== PERFORMING LOAD HOISTING OF INVARIANTS + ADVANCED!! ===\n\n";
  //   // #endif

  //   std::string updaterNodeName = "hoist(" + std::to_string(loopIdx) + ")";
    
  //   int loadInstructionIdx = 0;

  //   for (auto invariantLoadIter : invariantLoads) {

  //     // For each of the detected almost invariant loads
  //     Instruction *invariantLoad = invariantLoadIter.first;
  //     llvm::SSAUpdater* loadSSAUpdater = new llvm::SSAUpdater();

  //     std::string loadUpdaterNodeName = updaterNodeName + "(" + std::to_string(loadInstructionIdx) + ")";

  //     loadSSAUpdater->Initialize(invariantLoad->getType(), loadUpdaterNodeName + "(0)");

  //     // #ifdef DEBUG
  //       errs() << "\nFixing up almost invariant load: " << *invariantLoad << "\n";
  //       errs() << "LoadSSAUpdaterName: " << loadUpdaterNodeName << "\n";
  //     // #endif
      
  //     // Will be continiously hoisting up as many instructions as we can
  //     // We start by hoisting the almost invariant load
  //     // Need to fix up by add instruction after infrequent store and using SSAUpdater 
  //     std::queue<hoistInstructionInfo> hoistedInstructionQueue;

  //     hoistedInstructionQueue.push({invariantLoad, loadSSAUpdater, nullptr, true, -1});

  //     int hoistInstructionIdx = 1;

  //     while (!hoistedInstructionQueue.empty()) {

  //       hoistInstructionInfo hoistInstruction = hoistedInstructionQueue.front();

  //       errs() << "\nHOSTING NEW INSTRUCTION: " << *hoistInstruction.I;
  //       errs() << "\nLOCATED IN BASIC BLOCK: ";
  //       hoistInstruction.I->getParent()->printAsOperand(errs()); 
  //       errs() << "\n";


  //       // i. Hoist instruction to the end of the pre-header
  //       //    Placing clone of load instruction at the end of pre-header (Before the terminator)
  //       //    Will update SSAUpdater to indicate new value calcualted in PreHeader
  //       OLDcloneInstructionToPreheader(PreHeaderBlock, hoistInstruction);


  //       // ii. Recompute instruction at the infrequent blocks that the stores occur
  //       //     Places instruction at end of BB with infrequent store for recomputation
  //       //     Will update SSAUpdater to indicate new value calcualted in each BB it is placed in
  //       OLDcloneInstructionAfterInfrequentStore(invariantLoadIter.second, hoistInstruction);


  //       // iii. Need to update all instructions that used original load instruction
  //       //      instructionSSAUpdater now contains all proper redeclerations of returned value
  //       //      All instructions dependent on original instruction now need to look at instructionSSAUpdater value
  //       //      Will also determine if instruction can now also be hoisted (Within loop and is now truly LICM)
  //       OLDupdateDependentInstructions(loop_info, hoistInstruction, hoistedInstructionQueue, loadUpdaterNodeName, hoistInstructionIdx);


  //       // iv. Now all depend instructions looking at SSAUpdater Value instead
  //       //     Instruction has been properly hoisted and we can now safely delete original instruction
  //       errs() << "ERASING INSTRUCTION SAFELY\n";
  //       hoistInstruction.I->eraseFromParent();    

  //       // delete instructionSSAUpdater;
  //       hoistedInstructionQueue.pop();

  //     }

  //     ++loadInstructionIdx;
  //   }
  // }


  // void
  // OLDcloneInstructionToPreheader(
  //   BasicBlock* PreHeaderBlock,
  //   hoistInstructionInfo &hoistInstruction
  // )
  // {
  //   // #ifdef DEBUG
  //   errs() << "\n[BEGIN] ADD INSTRUCTION AT END OF PREHEADER\n\n";
  //   // #endif

  //   printBasicBlockInstructions("ORIGINAL PREHEADER", PreHeaderBlock);

  //   Instruction* clonedInstForPreHeader = hoistInstruction.I->clone();
  //   clonedInstForPreHeader->insertBefore(PreHeaderBlock->getTerminator());

  //   // Updating dependent instruction to look SSAUpdater value
  //   if (!hoistInstruction.isOriginalLoad) {
  //     hoistInstruction.dependentSSAUpdater->RewriteUseAfterInsertions(dyn_cast<llvm::User>(clonedInstForPreHeader)->getOperandUse(hoistInstruction.operandIdxUpdating));
  //   }

  //   printBasicBlockInstructions("AFTER LOAD INSERTION PREHEADER", PreHeaderBlock);

  //   hoistInstruction.ownSSAUpdater->AddAvailableValue(PreHeaderBlock, clonedInstForPreHeader);
    
  //   // #ifdef DEBUG
  //     errs() << "\n[END] ADD INSTRUCTION AT END OF PREHEADER\n\n";
  //   // #endif
  // }


  // void
  // OLDcloneInstructionAfterInfrequentStore(
  //   std::set<llvm::Instruction *> &associatedInfrequentStoreInstructions,
  //   hoistInstructionInfo &hoistInstruction
  // )
  // {
  //   // #ifdef DEBUG
  //   errs() << "\n[BEGIN] ADDING INSTRUCTION AT INFREQUENT BLOCKS WITH STORE\n\n";
  //   // #endif

  //   for (auto infrequentStoreIter : associatedInfrequentStoreInstructions) {

  //     BasicBlock *InfrequentBlockWithStore = infrequentStoreIter->getParent();

  //     // #ifdef DEBUG
  //       errs() << "Cloning load instruction after infrequent store block ";
  //       InfrequentBlockWithStore->printAsOperand(errs());
  //       errs() << "\n";
        
  //       printBasicBlockInstructions("ORIGINAL INFREQUENT BLOCK", InfrequentBlockWithStore);
  //     // #endif

  //     Instruction* cloneInstForInfrequentBlock = hoistInstruction.I->clone();
  //     cloneInstForInfrequentBlock->insertBefore(InfrequentBlockWithStore->getTerminator());

  //     // Updating dependent instruction to look SSAUpdater value
  //     if (!hoistInstruction.isOriginalLoad) {
  //       hoistInstruction.dependentSSAUpdater->RewriteUseAfterInsertions(dyn_cast<llvm::User>(cloneInstForInfrequentBlock)->getOperandUse(hoistInstruction.operandIdxUpdating));
  //     }

  //     // #ifdef DEBUG
  //       printBasicBlockInstructions("INFREQUENT BLOCK AFTER LOAD INSERTION", InfrequentBlockWithStore);
  //     // #endif

  //     hoistInstruction.ownSSAUpdater->AddAvailableValue(InfrequentBlockWithStore, cloneInstForInfrequentBlock);
  //   }

  //   // #ifdef DEBUG
  //     errs() << "\n[END] ADDING LOADS AT INFREQUENT BLOCKS WITH STORE\n";
  //   // #endif
  // }


  // void
  // OLDupdateDependentInstructions(
  //   Loop *loop_info,
  //   hoistInstructionInfo &hoistInstruction,
  //   std::queue<hoistInstructionInfo> &hoistedInstructionQueue,
  //   const std::string &loadUpdaterNodeName,
  //   int &hoistInstructionIdx
  // )
  // {
  //  // #ifdef DEBUG
  //  errs() << "\n[BEGIN] UPDATE ALL DEPENDENT INSTRUCTION TO LOOK AT SSAUPDATER\n";
  //  // #endif

  //  // Going through all instructions that depend on hoisted instruction
  //  for (auto U : hoistInstruction.I->users()) { // U is of type User *
  //    if (auto otherI = dyn_cast<Instruction>(U)) {  // Recasting as instruction

  //     // #ifdef DEBUG
  //       errs() << "\n(DEPENDENT INSTRUCTION) " << *otherI << "\n";
  //       errs() << "Located at Basic Block: ";
  //       otherI->getParent()->printAsOperand(errs());
  //       errs() << "\n\n";
  //     // #endif
      
  //     if (std::string(otherI->getOpcodeName()) == "phi") {
  //       // #ifdef DEBUG
  //         errs() << "PHI NODE DETECTED, SKIPPING\n";
  //       // #endif

  //       continue;
  //     }

  //     int operandIdxToUpdate = -1;

  //     for (int operandIdx = 0; operandIdx < otherI->getNumOperands(); ++operandIdx) {
  //       if (otherI->getOperand(operandIdx) == hoistInstruction.I) {
  //         operandIdxToUpdate = operandIdx;
  //         break;
  //       }
  //     }

  //     if (operandIdxToUpdate == -1) {
  //       errs() << "OPERAND TO UPDATE NOT FOUND\n";
  //       exit(1);
  //     }

  //     // #ifdef DEBUG
  //       printBasicBlockInstructions("ORIGINAL USE OF ORGINAL INSTRUCTION", otherI->getParent());
  //     // #endif

  //     // Updating dependent instruction to look SSAUpdater value
  //     hoistInstruction.ownSSAUpdater->RewriteUse(U->getOperandUse(operandIdxToUpdate));
    
  //     // #ifdef DEBUG
  //       printBasicBlockInstructions("UPDATED VALUE AFTER ACCOUNTING FOR PHI NODE", otherI->getParent());
  //     // #endif
      
  //     // TODO:
  //     // There is going to be more conditions to be determined if this instruction can be hoisted
  //     // If there is only ONE operand, then it can definently be hoisted
  //     // If the other operand is a constant, then it can definently be hoisted
  //     // BUT IF THERE IS MULTIPLE NOT CONSTANT OPERANDS --> PROBLEM

  //     // If the dependent instruction is not in the same basic block, will not hoist
  //     if (otherI->getParent() != hoistInstruction.I->getParent()) continue;


  //     // Going through each operand to determine if instruction is same to hoist
  //     bool safeToHoist = true;

  //     for (int operandIdx = 0; operandIdx < otherI->getNumOperands(); ++operandIdx) {

  //       // The phi node update is not loop invariant
  //       if (operandIdx == operandIdxToUpdate) continue;
        
  //       Value* operandValue = otherI->getOperand(operandIdx);

  //       errs() << "OPERAND VALUE: ";
  //       operandValue->printAsOperand(errs());
  //       errs() << "\n";

  //       // If operand is a constant, it is safe to hoist
  //       // if(llvm::isa<llvm::Constant>(operandValue)) {
  //       //   errs() << "OPERAND IS A CONSTANT\n";
  //       //   continue;
  //       // }

  //       if (!loop_info->isLoopInvariant(operandValue)) {
  //         safeToHoist = false;
  //         break;
  //       }
  //     }

  //     if (safeToHoist) {
  //       errs() << "\nINSTRUCTION IS HOISTABLE!!!\n";
  //       errs() << "PLACING INSTRUCTION IN HOIST QUEUE: " << *otherI << "\n\n";
        
  //       llvm::SSAUpdater* newSSAUpdater = new llvm::SSAUpdater();

  //       std::string updaterNodeName = loadUpdaterNodeName + "(" + std::to_string(hoistInstructionIdx++) + ")";

  //       newSSAUpdater->Initialize(otherI->getType(), updaterNodeName);

  //       hoistedInstructionQueue.push({otherI, newSSAUpdater, hoistInstruction.ownSSAUpdater, false, operandIdxToUpdate});
  //     }
  //    }
  //  }
   
  //  // #ifdef DEBUG
  //    errs() << "\n[END] UPDATE DEPENDENT INSTRUCTION TO LOOK AT SSAUPDATER\n";
  //  // #endif 
  // }


//   void 
//   basicAnalysis(
//     Function &F, 
//     FunctionAnalysisManager &FAM,
//     llvm::BlockFrequencyAnalysis::Result &bfi,
//     llvm::BranchProbabilityAnalysis::Result &bpi,
//     llvm::LoopAnalysis::Result &li) 
//   {

//     for (BasicBlock &BB : F) {
//       // errs() << "\n== BASIC BLOCK INFO ==\n";
//       // errs() << "Label Start: ";
//       // BB.printAsOperand(errs(), false);
//       // errs() << "\n";
//       // // errs() << "BB Name: " << BB.getName() << "\n";
//       // errs() << "Num Instructions: " << BB.size() << "\n";
      
//       // BlockFrequencyAnalysis Results
//       // errs() << "\n== BLOCK FREQUENCY ANALYSIS ==\n";
//       // // errs() << "Block Frequency: " << bfi.getBlockFreq(&BB).getFrequency() << " (Not useful on its own)\n";
//       // errs() << "Block Profile Count: " << bfi.getBlockProfileCount(&BB) << "\n";
//       // errs() << "Is Irreducible Header: " << bfi.isIrrLoopHeader(&BB) << "\n";

//       // BranchProbabilityAnalysis Results
//       // errs() << "\n== BRANCH PROBABILITY ANALYSIS ==\n";
//       Instruction* terminator_inst = BB.getTerminator();

//       if (terminator_inst->getOpcode() == Instruction::Br) {

//         for (unsigned i = 0; i < terminator_inst->getNumSuccessors(); ++i) {

//           BasicBlock *Succ = terminator_inst->getSuccessor(i);
//           BranchProbability Prob = bpi.getEdgeProbability(&BB, Succ);
//           double prob_double = (double) Prob.getNumerator() / (double) Prob.getDenominator();

//           // errs() << "Branch from Block ";
//           // BB.printAsOperand(errs(), false); 
//           // errs() << " to Block " ;
//           // Succ->printAsOperand(errs(), false);
//           // errs() << " has probability " << format("%.3f", prob_double);
          
//           // Check whether this edge out of the source block is 'hot'.
//           // Has a relative probability >= 80%.
//           // if (bpi.isEdgeHot(&BB, Succ)) {  (NOTE EDGE IS HOT HAS WIERD BEHAVIOR WHEN AT 0.8)
//           if (prob_double > 0.79) {
//             // errs() << " (Edge is Hot)";
//           }
//           // errs() << "\n";
//         }
//       }

//       // errs() << "\n== LOOP ANALYSIS ==\n";
//       // errs() << "BB is a loop header node: " << li.isLoopHeader(&BB) << "\n";
//       // errs() << "BB loop depth: " << li.getLoopDepth(&BB) << "\n";

//       // errs() << "\n== INSTRUCTIONS ==\n";
//       for (Instruction &I : BB) {
//         // errs() << I << "\n";
//       }
//       // errs() << "\n-----------------------\n";
//     }
//   }

}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, ModulePassManager &FPM,
        ArrayRef<PassBuilder::PipelineElement>) {
          if(Name == "fplicm-correctness"){
            FPM.addPass(HW2CorrectnessPass());
            return true;
          }
          // if(Name == "fplicm-performance"){
          //   FPM.addPass(HW2PerformancePass());
          //   return true;
          // }
          return false;
        }
      );
    }
  };
}