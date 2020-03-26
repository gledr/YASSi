#include "yassi_beginend.hpp"

using namespace Yassi::OptPass::Replay;

char BeginEndPass::ID = 0;

BeginEndPass::BeginEndPass():
    ReplayBase(), llvm::ModulePass(BeginEndPass::ID) 
{

}

BeginEndPass::~BeginEndPass() 
{

}

bool BeginEndPass::runOnModule(llvm::Module& M) 
{
    llvm::FunctionType* begin_sim_type = llvm::TypeBuilder<void(), false>::get(M.getContext());
    llvm::Function* begin_sim_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_BEGIN_SIM, begin_sim_type));
  
    llvm::FunctionType* end_sim_type = llvm::TypeBuilder<void(void), false>::get(M.getContext());
    llvm::Function* end_sim_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_END_SIM, end_sim_type));
    
    llvm::BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();
    
    std::vector<llvm::Value*> begin_sim_params;
    llvm::CallInst::Create(begin_sim_fun, begin_sim_params, "", llvm::cast<llvm::Instruction>(insertpos));

    llvm::Function::iterator insertpos_f = M.getFunction("main")->end();
    insertpos_f--;
    llvm::BasicBlock::iterator insertpos_b = insertpos_f->end();
    insertpos_b--;

    std::vector<llvm::Value*> end_sim_params;
    llvm::CallInst::Create(end_sim_fun, end_sim_params, "", llvm::cast<llvm::Instruction>(insertpos_b));

    return false;
}
