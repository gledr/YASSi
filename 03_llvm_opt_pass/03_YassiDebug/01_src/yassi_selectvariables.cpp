#include "yassi_debug_pass.hpp"

using namespace Yassi::OptPass::Debug;
using namespace Yassi::Utils;

char SelectVariables::ID = 0;
char LoopLatchParser::ID = 0;

/*
 * Use for the communication between the insert_select_variables pass and the loop_latch_info pass
 */
std::vector<llvm::Instruction*> IgnoredInstructionsInLoop;

LoopLatchParser::LoopLatchParser():
    FunctionPass(ID)
{
    
}

LoopLatchParser::~LoopLatchParser()
{
    
}

bool LoopLatchParser::runOnFunction(llvm::Function& F)
{
    p_verbose && std::cerr << "LoopLatchParser" << std::endl; fflush(stderr);
    p_verbose && std::cerr << "Executing LoopHeader pass ...\n";
     
    llvm::LoopInfoWrapperPass * LIWP = getAnalysisIfAvailable<llvm::LoopInfoWrapperPass> ();
    llvm::LoopInfo & LI = LIWP->getLoopInfo();
      
    for (llvm::LoopInfo::iterator i = LI.begin(), e = LI.end(); i!=e; ++i){
        AnalyseLoop(*i, 0);
    }
    
    p_verbose && std::cerr << "Found " << IgnoredInstructionsInLoop.size() << " to be ingored in loops\n";
    
    return false;
}

void LoopLatchParser::getAnalysisUsage(llvm::AnalysisUsage& AU) const
{
    AU.addRequired<llvm::LoopInfoWrapperPass>();
    AU.setPreservesAll();
}

void LoopLatchParser::AnalyseLoop(llvm::Loop* L, size_t nesting)
{
    llvm::BasicBlock::iterator I = L->getLoopLatch()->begin();
      
    for (; I != L->getLoopLatch()->end(); ++ I){
        if(llvm::isa<llvm::BinaryOperator>(I)){
            IgnoredInstructionsInLoop.push_back(llvm::cast<llvm::Instruction>(I));
        }
    }

    I = L->getHeader()->begin();
    for(; I != L->getHeader()->end(); ++I){
        if (llvm::isa<llvm::ICmpInst>(I)){
               IgnoredInstructionsInLoop.push_back(llvm::cast<llvm::Instruction>(I));
        }
    }

    llvm::BranchInst *BI = llvm::dyn_cast<llvm::BranchInst>(L->getLoopLatch()->getTerminator());
    llvm::BasicBlock *next_block = BI->getSuccessor(0);

    for(auto itor = next_block->begin(); itor != next_block->end(); ++itor){
        if(llvm::isa<llvm::ICmpInst>(itor)){
        IgnoredInstructionsInLoop.push_back(llvm::cast<llvm::Instruction>(itor));
        }
    }     
}

SelectVariables::SelectVariables():
    BasePass(), ModulePass(ID)
{
   p_blacklisted_lines = p_db->get_blacklisted_lines();
}

SelectVariables::~SelectVariables()
{
    
}

bool SelectVariables::runOnModule(llvm::Module& M)
{
    std::vector<ReplaceAfter> values_to_replace;
    //dump_blacklisted_lines();
    for (llvm::Module::iterator fn = M.begin(); fn != M.end(); ++fn ){
        for (llvm::Function::iterator bb = fn->begin(); bb != fn->end(); ++bb){
            for (llvm::BasicBlock::iterator in = bb->begin(); in != bb->end(); ++in){
                if (blacklisted_instruction(*in)){
                    continue;
                }
                if(llvm::isa<llvm::BinaryOperator>(in)){
                    p_verbose && std::cerr << "Binary Operator Detected! (" << in->getName().str() << ")" << std::endl;;

                    // Search in the extracted data by loop_latch_info if the binary instruction is part of a loop latch.
                    // Iff it is part of a loop latch we are not inserting select variables, since this would end up in an endless loop
                    // as the SAT solver can insert arbitrary values and the loop will never terminate
                    if(std::find(IgnoredInstructionsInLoop.begin(), IgnoredInstructionsInLoop.end(), llvm::cast<llvm::Instruction>(in)) == IgnoredInstructionsInLoop.end()){
                        p_verbose && std::cerr << "No loop latch is using this\n";
                        llvm::BasicBlock::iterator insertpos = in; insertpos++;
                        std::string linenum = BaseUtils::decode_constant(this->line_number_of_instruction(*in));
                        llvm::AllocaInst* enable_ptr = new llvm::AllocaInst(llvm::Type::getInt1Ty( M.getContext() ), 0, linenum + "_select_enable", llvm::cast<llvm::Instruction>(insertpos));
                        llvm::AllocaInst* val_ptr    = new llvm::AllocaInst(in->getType(), 0, linenum + "_select_value", llvm::cast<llvm::Instruction>(insertpos));

                        llvm::LoadInst* enable = new llvm::LoadInst(enable_ptr,"",llvm::cast<llvm::Instruction>(insertpos));
                        llvm::LoadInst* val = new llvm::LoadInst(val_ptr,"",llvm::cast<llvm::Instruction>(insertpos));
        
                        llvm::SelectInst * SelectInstruction =  llvm::SelectInst::Create (enable,val, llvm::cast<llvm::Instruction>(in), "select_result", llvm::cast<llvm::Instruction>(insertpos));

                        // As we manipulate the result of a binary instruction we also have to make sure, that our introduces result
                        // ends up in the indtended register!
                        ReplaceAfter val_to_repl = {llvm::cast<llvm::Instruction>(in), SelectInstruction };
                        values_to_replace.push_back(val_to_repl);
                
                    } else {
                        p_verbose && std::cerr << "Instruction used in loop latch!\n";
                    }    

                    p_verbose && std::cerr << "Value ID: " << in->getValueID() << "\n";
                    p_verbose && std::cerr << "Address" << llvm::cast<llvm::Instruction>(in) << "\n";  
                } else if (llvm::isa<llvm::ICmpInst>(in)){
                    p_verbose && std::cerr << "Compare Operator Detected! (" << in->getName().str() << ")" << std::endl;
    
                    if(std::find(IgnoredInstructionsInLoop.begin(), IgnoredInstructionsInLoop.end(), llvm::cast<llvm::Instruction>(in)) == IgnoredInstructionsInLoop.end()){
                        p_verbose && std::cerr << "No loop latch is using this\n";
                        llvm::BasicBlock::iterator insertpos = in; insertpos++;
        
                        std::string linenum = BaseUtils::decode_constant(this->line_number_of_instruction(*in));
                        llvm::AllocaInst* enable_ptr = new llvm::AllocaInst(llvm::Type::getInt1Ty( M.getContext() ), 0, linenum +"_select_enable", llvm::cast<llvm::Instruction>(insertpos));
                        llvm::AllocaInst* val_ptr    = new llvm::AllocaInst(in->getType(), 0, linenum + "_select_value", llvm::cast<llvm::Instruction>(insertpos));

                        llvm::LoadInst* enable = new llvm::LoadInst(enable_ptr,"",llvm::cast<llvm::Instruction>(insertpos));
                        llvm::LoadInst* val = new llvm::LoadInst(val_ptr,"",llvm::cast<llvm::Instruction>(insertpos));
        
                        llvm::SelectInst * SelectInstruction =  llvm::SelectInst::Create (enable,val, llvm::cast<llvm::Instruction>(in), "select_result", llvm::cast<llvm::Instruction>(insertpos));

                        // As we manipulate the result of a binary instruction we also have to make sure, that our introduces result
                        // ends up in the indtended register!
                        ReplaceAfter val_to_repl = {llvm::cast<llvm::Instruction>(in), SelectInstruction };
                        values_to_replace.push_back(val_to_repl);
    
                    } else {
                        p_verbose && std::cerr << "Instruction used in loop latch!\n";
                    }

                    p_verbose && std::cerr << "Value ID: " << in->getValueID() << "\n";
                    p_verbose && std::cerr << "Address" << llvm::cast<llvm::Instruction>(in) << "\n";
                }
            }
        }
    }
    
    // Replace intstruction target registers - with the introduction of select statements the targets have been changed
    for(std::vector<ReplaceAfter>::iterator it = values_to_replace.begin(); it != values_to_replace.end(); it++ ){
        llvm::Instruction* instr_to_replace = it->instr_to_replace;
        llvm::Instruction* replace_by = it->replace_by;

        for (llvm::Value::user_iterator i = instr_to_replace->user_begin(), e = instr_to_replace->user_end(); i != e; ++i){
            llvm::Instruction *instruction = llvm::dyn_cast<llvm::Instruction>( *i );
            
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


bool SelectVariables::blacklisted_instruction(llvm::Instruction const & ins)
{
    std::string line = this->line_number_of_instruction(ins);
   
	if (line != "-1"){
	  if(std::find(p_blacklisted_lines.begin(), p_blacklisted_lines.end(), line) == p_blacklisted_lines.end()){
		return false;
        
	  } else{

		p_verbose && std::cerr << "Instruction: " << ins.getName().str() << "\n";
		p_verbose && std::cerr << "@LineNum: " << line << "\n";
		p_verbose && std::cerr << "Is BLACKLISTED\n";
		return true;
	  }
	} else {
	  return false;
	}
}

void SelectVariables::dump_blacklisted_lines()
{
    for(size_t i = 0; i < p_blacklisted_lines.size(); ++i){
        llvm::errs () << p_blacklisted_lines[i] << "\n";
	}
}
