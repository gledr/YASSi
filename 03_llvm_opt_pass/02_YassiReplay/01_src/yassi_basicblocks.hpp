#ifndef YASSI_BASICBLOCKS_PASS_HPP
#define YASSI_BASICBLOCKS_PASS_HPP

#include "yassi_replaybase.hpp"

namespace Yassi::OptPass::Replay {

class BasicBlocksPass: public virtual ReplayBase, public llvm::ModulePass {
public:
    BasicBlocksPass();

    virtual ~BasicBlocksPass();

    bool runOnModule(llvm::Module & M) override;

private:
    static char ID; 
};

}

#endif /* YASSI_BASICBLOCKS_PASS_HPP */
