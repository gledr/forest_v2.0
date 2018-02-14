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
 *      ,---,
 *   (_,\/_\_/_\     Author:   Pablo Gonzlez de Aledo (), pablo.aledo@gmail.com
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

#define DEBUG
#define BLACKLIST

using namespace llvm;
using namespace std;

/*
 * Use for the communication between the insert_select_variables pass and the loop_latch_info pass
 */
std::vector<Instruction*> IgnoredInstructionsInLoop;

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
      errs () << "Found " << IgnoredInstructionsInLoop.size() << " to be ingored in loops\n";
#endif
      return false;
    }

  private: 
    void AnalyseLoop (Loop * L, size_t nesting) {
      BasicBlock::iterator I = L->getLoopLatch()->begin();
      
      for (; I != L->getLoopLatch()->end(); ++ I){
      	if(BinaryOperator::classof(I)){
		  IgnoredInstructionsInLoop.push_back(I);
      	}
      }

	  I = L->getHeader()->begin();
	  for(; I != L->getHeader()->end(); ++I){
		if (ICmpInst::classof(I)){
		  IgnoredInstructionsInLoop.push_back(I);
		}
	  }

	  BranchInst *BI = dyn_cast<BranchInst>(L->getLoopLatch()->getTerminator());
	  BasicBlock *next_block = BI->getSuccessor(0);

	  for(auto itor = next_block->begin(); itor != next_block->end(); ++itor){
		errs () << *itor << "\n";
		if(ICmpInst::classof(itor)){
		  errs () << "Is Compare\n";
		  IgnoredInstructionsInLoop.push_back(itor);
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
  SelectVariables() : ModulePass(ID) {
	this->read_blacklist("/dev/shm/forest/blacklist.txt");
  }

  std::vector<int> p_blacklisted_lines;

  void read_blacklist(std::string const & blacklist_file){
	std::fstream in_file(blacklist_file, std::ios::in);
	std::string line;
	while(std::getline(in_file, line)){
	  std::stringstream tmp;
	  tmp << line;
	  int as_int;
	  tmp >> as_int;
	  p_blacklisted_lines.push_back(as_int);
	}
  }

  bool blacklisted_instruction (Instruction const & ins){
	DebugLoc debug_infos = ins. getDebugLoc();

	if (debug_infos.get()){
	  size_t line_num = debug_infos. getLine();
	  if(std::find(p_blacklisted_lines.begin(), p_blacklisted_lines.end(), line_num ) == p_blacklisted_lines.end()){
		return false;
	  } else{
#ifdef BLACKLIST
		errs () << "Instruction: " << ins << "\n";
		errs () << "@LineNum: " << line_num << "\n";
		errs () << "Is BLACKLISTED\n";
#endif
		return true;
	  }
	} else {
	  return false;
	}
  }

  void dump_blacklisted_lines () {
	for(size_t i = 0; i < p_blacklisted_lines.size(); ++i){
	  errs () << p_blacklisted_lines[i] << "\n";
	}
  }
  
  virtual bool runOnModule(Module &M) {
 
    vector<ReplaceAfter> values_to_replace;
	// dump_blacklisted_lines();
    for (Module::iterator fn = M.begin(); fn != M.end(); ++fn ){
	  for (Function::iterator bb = fn->begin(); bb != fn->end(); ++bb){
		for (BasicBlock::iterator in = bb->begin(); in != bb->end(); ++in){
		  if (blacklisted_instruction(*in)){
			continue;
		  }
		  if(BinaryOperator::classof(in)){
#ifdef DEBUG
			errs () << "Binary Operator Detected!\n";
			errs () << *in << "\n";
#endif
			// Search in the extracted data by loop_latch_info if the binary instruction is part of a loop latch.
			// Iff it is part of a loop latch we are not inserting select variables, since this would end up in an endless loop
			// as the SAT solver can insert arbitrary values and the loop will never terminate
			if(std::find(IgnoredInstructionsInLoop.begin(), IgnoredInstructionsInLoop.end(), in) == IgnoredInstructionsInLoop.end()){
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
			errs () << "Compare Operator Detected!\n";
			errs () << *in << "\n";
#endif

						if(std::find(IgnoredInstructionsInLoop.begin(), IgnoredInstructionsInLoop.end(), in) == IgnoredInstructionsInLoop.end()){
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


GlobalVariable* make_global_str(Module& M, string name){

	uint64_t length = (uint64_t) name.length()+1;
	//cerr << "---------------------" << name << "---------" << length << endl;
	ArrayType* ArrayTy_0 = ArrayType::get(IntegerType::get(M.getContext(), 8), length );

	GlobalVariable* gvar_array_a = new GlobalVariable(/*Module=*/M,
			/*Type=*/ArrayTy_0,
			/*isConstant=*/false,
			/*Linkage=*/GlobalValue::ExternalLinkage,
			/*Initializer=*/0, // has initializer, specified below
			/*Name=*/"a");

	Constant* const_array_2 = ConstantDataArray::getString(M.getContext(), name.c_str(), true);

	// Global Variable Definitions
	gvar_array_a->setInitializer(const_array_2);

	return gvar_array_a;

}

Constant* pointerToArray( Module& M, GlobalVariable* global_var ){
	ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
	std::vector<Constant*> const_ptr_9_indices;
	const_ptr_9_indices.push_back(const_int64_10);
	const_ptr_9_indices.push_back(const_int64_10);

	Constant* const_ptr_9 = ConstantExpr::getGetElementPtr(NULL, global_var, const_ptr_9_indices);

	return const_ptr_9;
}


struct InjectResults : public ModulePass {
  static char ID;
  InjectResults() : ModulePass(ID) {}

  int const pos_load_value   = 1;
  int const pos_load_enable  = 2;
  int const pos_alloc_value  = 3;
  int const pos_alloc_enable = 4;
  
  virtual bool runOnModule(Module &M) {

   
	Constant* nondet_int = M.getOrInsertFunction("__VERIFIER_nondet_int" , Type::getInt32Ty(M.getContext()), Type::getInt8PtrTy(M.getContext()), NULL);
	Function* hook_value = dyn_cast<Function>(nondet_int);

	Constant* nondet_bool = M.getOrInsertFunction("__VERIFIER_nondet_bool" , Type::getInt1Ty(M.getContext()), Type::getInt8PtrTy(M.getContext()), NULL);
	Function* hook_enable = dyn_cast<Function>(nondet_bool);

	std::vector<int> select_var_positions;
	std::vector<BasicBlock::iterator> found_select_variables;

	for (Module::iterator fn = M.begin(); fn != M.end(); ++fn ){
	  for (Function::iterator bb = fn->begin(); bb != fn->end(); ++bb){
#ifdef DEBUG
		errs () << "Basic Block\n";
#endif
		int select_var_pos = 0;
		size_t found_select_variables_cnt = found_select_variables.size();
		for (BasicBlock::iterator in = bb->begin(); in != bb->end(); ++in){
		  	select_var_pos++;
		  if(SelectInst::classof(in)){
			if(std::find(found_select_variables.begin(), found_select_variables.end(), in) == found_select_variables.end()){
#ifdef DEBUG
			  errs () << *in << "\n";
#endif			 
			  select_var_positions.push_back(select_var_pos+ 4*(select_var_positions.size()));
			  found_select_variables.push_back(in);
			}
		  }
		}
		if (found_select_variables_cnt == found_select_variables.size()){
		  continue;
		}
#ifdef DEBUG
		errs () << "Found " << select_var_positions.size() << " select variables\n";
#endif
		for(std::vector<int>::const_iterator itor = select_var_positions.begin(); itor != select_var_positions.end(); ++itor){
		  int cnt = 0;
		  Instruction* alloc_enable;
		  for(BasicBlock::iterator in = bb->begin(); cnt != *itor - pos_alloc_enable; ++in){
			++cnt;
			alloc_enable = in;
		  }
#ifdef DEBUG
		  errs () << *alloc_enable << "\n";
#endif

		  cnt = 0;
		  Instruction * alloc_value;
		  for(BasicBlock::iterator in = bb->begin(); cnt != *itor - pos_alloc_value; ++in){
			++cnt;
			alloc_value = in;
		  }
#ifdef DEBUG
		  errs () << *alloc_value << "\n";
#endif
		  cnt = 0;
		  Instruction * top_load_enable;
		  for(BasicBlock::iterator in = bb->begin(); cnt != *itor - pos_load_enable; ++in){
			++cnt;
			top_load_enable = in;
		  }
#ifdef DEBUG
		  errs () << *top_load_enable << "\n";
#endif
		  cnt = 0;
		  Instruction * top_load_value;
		  for(BasicBlock::iterator in = bb->begin(); cnt != *itor - pos_load_value; ++in){
			++cnt;
			top_load_value = in;
		  }
#ifdef DEBUG
		  errs () << *top_load_value << "\n";
#endif
		  GlobalVariable* global_val_value = make_global_str(M, alloc_value->getName());
		  std::vector<Value*> params_value;
		  params_value.push_back(pointerToArray(M,global_val_value));
		  Instruction *call_replace_value = CallInst::Create(hook_value, params_value, "");
		  call_replace_value->insertAfter(alloc_value);

		  GlobalVariable* global_val_enable = make_global_str(M, alloc_enable->getName());
		  std::vector<Value*> params_enable;
		  params_enable.push_back(pointerToArray(M,global_val_enable));
		  Instruction *call_replace_enable = CallInst::Create(hook_enable, params_enable,  "");
		  call_replace_enable->insertAfter(alloc_enable);
	
		  StoreInst* store_value =  new StoreInst(call_replace_value,  alloc_value,  top_load_value);
		  StoreInst* store_enable = new StoreInst(call_replace_enable, alloc_enable, top_load_enable);
		}	
	  }
	}
	return true;
  }
};

/*
 * @brief For a given result from the SAT solver find the line in the source code
 *
 * #TODO Since we are covering only one error by the time - multiple errors have not been considered here!
 *
 */
struct ReadDebugInformation : public ModulePass {
  static char ID;
  ReadDebugInformation() : ModulePass(ID) {};

  virtual bool runOnModule(Module & M){
	read_results("/tmp/smt/__allsat_results__");
	
	std::string result;
	for (auto itor = p_in_file.begin(); itor != p_in_file.end(); ++itor){
	  if (itor->reg_val == "true"){
		result = itor->reg_name;
		break;
	  }
	}
 
	for (Module::iterator fn = M.begin(); fn != M.end(); ++fn ){
	  for (Function::iterator bb = fn->begin(); bb != fn->end(); ++bb){
		int pos = 0;
		bool found_it = false;
		for (BasicBlock::iterator in = bb->begin(); in != bb->end(); ++in){
		  std::string reg_name = in->getName();
		  if (AllocaInst::classof(in) && reg_name.compare(result) == 0){
			found_it = true;
			pos--;
			break;		
		  }
		  pos++;
		}
		
		if(!found_it){		
		  continue;
		} else {	
		  int cnt = 0;
		  Instruction * op;
		  for (BasicBlock::iterator in = bb->begin(); in != bb->end(); ++in){
			if (cnt == pos){
			  op = in;
			  break;	
			}
			cnt++;
		  }
		  DebugLoc debug_info = op->getDebugLoc();
		  if(!debug_info.get()){
			errs () << "No Valid Location\n";
		  } else {
			std::fstream out_file("/tmp/smt/__resolved_allsat_solutions__", std::ios::out);
			out_file << debug_info.getLine() << std::endl;
			out_file.close();
			errs () << "Wrong line ist at: " << debug_info.getLine() << "\n";
          }
		}
	  }
  
  
	}
	return true;
  }

  void read_results (std::string const & filename){
	std::fstream in_file(filename, std::ios::in);
	std::string line;

	while(std::getline(in_file,line)){
	  SingleResultPair tmp;
	  std::string token = ",";
	  size_t pos = 0;

	  int cnt = 0;
	  while ((pos = line.find(token)) != std::string::npos){
		std::string key = line.substr(0, pos);
		if(cnt == 0){
		  tmp.reg_name = resolve_register_name(key);
		} else if (cnt == 1){
		  tmp.reg_val = key;
		} else if (cnt == 2){
		  std::stringstream sstream;
		  sstream << key;
		  sstream >> tmp.solution;
		
		} else if (cnt == 3){
		  tmp.path = key;
		}
		cnt++;
		line.erase(0, pos + 1); 
	  }
	  p_in_file.push_back(tmp);
	}

	in_file.close();
  }

  std::string resolve_register_name(std::string const & mangled_name){
	std::string main_register = "main_register";
	return mangled_name.substr(main_register.size()+1, mangled_name.size());
  }
  
  
  class SingleResultPair {
  public:
	std::string reg_name;
	std::string reg_val;
	int solution;
	std::string path;
  };
  std::vector<SingleResultPair> p_in_file;
  

};


// Identifiers
// Select Variables
char LoopLatchParser::ID = 0;
static RegisterPass<LoopLatchParser> LoopLatchParser(      "loop_latch_info"         , "Extract binary statements from the loop latch        " );

char SelectVariables::ID = 0;
static RegisterPass<SelectVariables> SelectVariables( "insert_select_variables" , "Inserts the free SAT variables for debugging         " );

char InjectResults::ID = 0;
static RegisterPass<InjectResults> InjectResults("inject_results", "Inserts results generated by SAT by calling a library function accessing the db");

char ReadDebugInformation::ID = 0;
static RegisterPass<ReadDebugInformation> ReadDebugInformation("read_debug", "read the debug information stored into the bytecode file");
