#include "yassi_basicblocks.hpp"

using namespace Yassi::OptPass::Replay;

char BasicBlocksPass::ID = 0;

BasicBlocksPass::BasicBlocksPass():  
    ReplayBase(), llvm::ModulePass(BasicBlocksPass::ID) 
{

}

BasicBlocksPass::~BasicBlocksPass () 
{

}

bool BasicBlocksPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            bool phi_node = false;
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                // @ sebastian: If there is a phi node in the block
                //              the begin_bb call must no be on top!
                if (llvm::isa<llvm::PHINode>(in)) {
                    phi_node = 1;
                    break;
                }
            }

            std::string namebb = bb->getName();
            std::string begin_bb = "begin_" + namebb;
            std::string end_bb = "end_" + namebb;
            
            llvm::GlobalVariable* c1 = this->make_global_str(M,begin_bb);
            llvm::GlobalVariable* c2 = this->make_global_str(M,end_bb);

            llvm::FunctionType* begin_bb_type = llvm::TypeBuilder<void(char*), false>::get(M.getContext());
            llvm::Function* begin_bb_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_BEGIN_BB, begin_bb_type));

            llvm::FunctionType* end_bb_type = llvm::TypeBuilder<void(char*), false>::get(M.getContext());
            llvm::Function* end_bb_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_END_BB, end_bb_type));
         
            llvm::BasicBlock::iterator insertpos_begin_fn = bb->begin();
            if (phi_node) {
                insertpos_begin_fn++;
            }
            
            std::vector<llvm::Value*> params_begin_fn;
            params_begin_fn.push_back(this->pointerToArray(M,c1));
            llvm::CallInst::Create(begin_bb_fun, params_begin_fn, "", llvm::cast<llvm::Instruction>(insertpos_begin_fn));
                
            llvm::BasicBlock::iterator insertpos_end_fn = bb->end();
            insertpos_end_fn--;
            std::vector<llvm::Value*> params_end_fn;
            params_end_fn.push_back(this->pointerToArray(M,c2));
            llvm::CallInst::Create(end_bb_fun, params_end_fn, "", llvm::cast<llvm::Instruction>(insertpos_end_fn));
        }
    }
    return false;
}
