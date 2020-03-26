#include "yassi_changeassigns.hpp"

using namespace Yassi::OptPass::Replay;
using namespace Yassi::Utils;


char ChangeAssignsPass::ID = 0;

ChangeAssignsPass::ChangeAssignsPass(): 
    ReplayBase(), llvm::ModulePass(ChangeAssignsPass::ID) 
{

}

ChangeAssignsPass::~ChangeAssignsPass() 
{

}

bool ChangeAssignsPass::runOnModule(llvm::Module& M) 
{
    std::map<std::string, std::string> names_from_position = load_names_from_pos();

    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {

                std::string actual_reg_name = fun->getName().str()  + MANGLING_SEPERATOR + in->getName().str();
                if(names_from_position[actual_reg_name] != "" ) {
                    std::string target_function;
                    if(fun->getName().str() == "test"){
                        target_function = p_current_source_file + MANGLING_SEPERATOR + "main";
                    } else {
                        target_function = fun->getName().str();
                    }
                    
                    std::string global_register_name = target_function + MANGLING_SEPERATOR + "register" + MANGLING_SEPERATOR + in->getName().str();
                    llvm::GlobalVariable* gvar_int32_global_a = M.getGlobalVariable(global_register_name);
                    llvm::BasicBlock::iterator insertpos = in;
                    insertpos++;
                    
                    
                    llvm::LoadInst* li = new llvm::LoadInst(gvar_int32_global_a, "", false, llvm::cast<llvm::Instruction>(insertpos));
                   
                    new llvm::StoreInst(li,llvm::cast<llvm::Instruction>(in), false, llvm::cast<llvm::Instruction>(insertpos));
                }
            }
        }
    }
    return false;
}

std::map<std::string, std::string> ChangeAssignsPass::load_names_from_pos() 
{
    std::map<std::string, std::string> ret;
    std::vector<VariableInfo> test_vector_variables = p_db->get_test_vector_variables();

    for(auto itor : test_vector_variables) {
        std::vector<std::string> tokens2 = BaseUtils::tokenize(itor.position, MANGLING_SEPERATOR);
        std::string position;

        if(tokens2[1] == "main") {
            position = "test" + MANGLING_SEPERATOR + tokens2[3];
        } else {
            position = tokens2[1] + MANGLING_SEPERATOR + tokens2[3];
        }

        std::string name = itor.name;
        ret[position] = name;
    }
    return ret;
}
