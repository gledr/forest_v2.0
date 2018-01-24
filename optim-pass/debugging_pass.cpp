/*
 * =====================================================================================
 * /
 * |     Filename:  optimization_pass.cpp
 * |
 * |  Description:
 * |
 * |      Version:  1.0
 * |      Created:  05/15/2013 05:27:39 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ♪♪  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#include <llvm/Pass.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallingConv.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/MathExtras.h>
#include <llvm/IR/Operator.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include "llvm/Analysis/LoopInfo.h"
#include <algorithm>
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <map>
#include <set>


#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;


#define DEBUG

/*
 * Use for the communication between the insert_select_variables pass and the loop_latch_info pass
 */
std::vector<Instruction*> BinInstructionsLoopLatch;

namespace {
  /*
   * This pass is needed to extract the information of used binary statements in loop latches.
   * Since we are depended on LoopInfo, we must use a FunctionPass for that - we can not integrate
   * that into our module passes. 
   * We have to call this pass using opt -load *-so -loop_latch_info before invoking the insert_select_variables
   * pass since we can not call it automatically from a Module Pass. 
   */
  struct LoopLatchParser : public FunctionPass {
    static char ID;
    LoopLatchParser() : FunctionPass(ID) {} 
    
    // Tell LLVM that we are dependent on LoopInfo
    void getAnalysisUsage (AnalysisUsage & AU) const {
      AU.addRequired<LoopInfoWrapperPass>();
      AU.setPreservesAll();
    }

    virtual  bool runOnFunction (Function &F)  {
#ifdef DEBUG
      errs () << "Executing LoopHeader pass ...\n";
#endif      
      LoopInfoWrapperPass * LIWP = getAnalysisIfAvailable<LoopInfoWrapperPass> ();
      LoopInfo & LI = LIWP->getLoopInfo();
      
      for (LoopInfo::iterator i = LI.begin(), e = LI.end(); i!=e; ++i){
	AnalyseLoop(*i, 0);
      }
#ifdef DEBUG
      errs () << "Found " << BinInstructionsLoopLatch.size() << " binary statementes in loops\n";
#endif
      return false;
    }

  private: 
    void AnalyseLoop (Loop * L, size_t nesting) {
      BasicBlock::iterator I = L->getLoopLatch()->begin();
      
      for (; I != L->getLoopLatch()->end(); ++ I){
      	if(BinaryOperator::classof(I)){
	  BinInstructionsLoopLatch.push_back(I);
      	}
      }
    }
    
  };
}

typedef struct ReplaceAfter {
  Instruction* instr_to_replace;
  Instruction* replace_by;
} ReplaceAfter;

struct SelectVariables: public ModulePass {
  static char ID;
  SelectVariables() : ModulePass(ID) {}
  
  virtual bool runOnModule(Module &M) {
 
    vector<ReplaceAfter> values_to_replace;
    
    mod_iterator(M, fn) {
      fun_iterator(fn, bb){
	blk_iterator(bb, in){

	  if(BinaryOperator::classof(in)){
#ifdef DEBUG
	    errs () << "Binary Operator Detected!\n";
	    errs () << *in << "\n";
#endif
	    // Search in the extracted data by loop_latch_info if the binary instruction is part of a loop latch.
	    // Iff it is part of a loop latch we are not inserting select variables, since this would end up in an endless loop
	    // as the SAT solver can insert arbitrary values and the loop will never terminate
	    if(std::find(BinInstructionsLoopLatch.begin(), BinInstructionsLoopLatch.end(), in) == BinInstructionsLoopLatch.end()){
#ifdef DEBUG
	      errs () << "No loop latch is using this\n";
#endif
	      BasicBlock::iterator insertpos = in; insertpos++;
	      
	      AllocaInst* enable_ptr = new AllocaInst(Type::getInt1Ty( M.getContext() ), "select_enable", insertpos);
	      AllocaInst* val_ptr    = new AllocaInst(in->getType(), "select_value", insertpos);
	
	      LoadInst* enable = new LoadInst(enable_ptr,"",insertpos);
	      LoadInst* val = new LoadInst(val_ptr,"",insertpos);
	      
	      SelectInst * SelectInstruction =  SelectInst::Create (enable,val, in, "select_result", insertpos);

	      // As we manipulate the result of a binary instruction we also have to make sure, that our introduces result
	      // ends up in the indtended register!
	      ReplaceAfter val_to_repl = {in, SelectInstruction };
	      values_to_replace.push_back(val_to_repl);
	      
	    } else {
#ifdef DEBUG
	      errs () << "Instruction used in loop latch!\n";
#endif
	    }
#ifdef DEBUG
	    errs () << "Value ID: " << in->getValueID() << "\n";
	    errs () << "Address" << in << "\n";
#endif	   
	  }
	  else if (ICmpInst::classof(in)){
#ifdef DEBUG
	    errs () << "Compare Instruction Detected!\n";
	    errs () << *in << "\n";
#endif
	  }
	}
      }
    }
    
    // Replace intstruction target registers - with the introduction of select statements the targets have been changed
    for( vector<ReplaceAfter>::iterator it = values_to_replace.begin(); it != values_to_replace.end(); it++ ){
      Instruction* instr_to_replace = it->instr_to_replace;
      Instruction* replace_by = it->replace_by;

      for (Value::user_iterator i = instr_to_replace->user_begin(), e = instr_to_replace->user_end(); i != e; ++i){
	Instruction *instruction = dyn_cast<Instruction>( *i );

	if( instruction == replace_by ) continue;

	for(size_t n = 0; n < instruction->getNumOperands(); n++ ){
	  if( instruction->getOperand(n) == instr_to_replace ){
	    instruction->setOperand(n, replace_by);
	  }
	}
      }
    }

    return false;
  }
};


// Identifiers
// Select Variables
char LoopLatchParser::ID = 0;
static RegisterPass<LoopLatchParser> LoopLatchParser(      "loop_latch_info"         , "Extract binary statements from the loop latch        " );

char SelectVariables::ID = 0;
static RegisterPass<SelectVariables> SelectVariables( "insert_select_variables" , "Inserts the free SAT variables for debugging         " );
