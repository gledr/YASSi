#include "yassi_branch.hpp"

using namespace Yassi::OptPass::Replay;

char BranchPass::ID = 0;

BranchPass::BranchPass(): 
    ReplayBase(), llvm::ModulePass(BranchPass::ID) 
{

}

BranchPass::~BranchPass() 
{

}

bool BranchPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {

                if(llvm::isa<llvm::BranchInst>(in) ) {
                    llvm::BranchInst* in_b = llvm::cast<llvm::BranchInst>(in);

                    if(in_b->isConditional()) {
                        std::vector<llvm::Type *> args (1, llvm::Type::getInt1Ty(M.getContext()));
                        llvm::FunctionType*cond_branch_type = llvm::FunctionType::get(llvm::Type::getVoidTy(M.getContext()), args, false);
                        llvm::Function* cond_branch_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_BRANCH_COND, cond_branch_type));
                
                        llvm::BasicBlock::iterator insertpos = in;

                        std::vector<llvm::Value*> params;
                        params.push_back(in_b->getCondition());

                        llvm::CallInst::Create(cond_branch_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
                    }
                }
            }
        }
    }
    return false;
}
