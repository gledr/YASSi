#include "yassi_removeforcefree.hpp"

using namespace Yassi::OptPass::Replay;

char RemoveForceFreePass::ID = 0;

RemoveForceFreePass::RemoveForceFreePass():  
    ReplayBase(), llvm::ModulePass(ID) 
{

}

RemoveForceFreePass::~RemoveForceFreePass() 
{

}

bool RemoveForceFreePass::runOnModule(llvm::Module& M) 
{
    std::vector<llvm::Instruction*> instr_to_rm;

    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::CallInst>(in) ) {
                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst>(in);

                    bool hasname = in_c->getCalledFunction();
                    std::string fn_name;
                    if(hasname) {
                        fn_name = in_c->getCalledFunction()->getName().str();
                        std::string demangled_name = this->demangle_fn_name(fn_name);
                        if(demangled_name == BACKEND_FN_FORCEFREE_LOCAL || demangled_name == BACKEND_FN_FORCEFREE_GLOBAL){
                            instr_to_rm.push_back(llvm::cast<llvm::Instruction>(in));
                        }
                    }
                }
            }
        }
    }

    for(auto it = instr_to_rm.begin(); it != instr_to_rm.end(); it++) {
        (*it)->eraseFromParent();
    }
    return false;
}
