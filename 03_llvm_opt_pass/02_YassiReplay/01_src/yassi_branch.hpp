#ifndef YASSI_BRANCH_PASS_HPP
#define YASSI_BRANCH_PASS_HPP

#include "yassi_replaybase.hpp"

namespace Yassi::OptPass::Replay {

class BranchPass: public llvm::ModulePass, public virtual ReplayBase {
public:
    BranchPass();

    virtual ~BranchPass();

    bool runOnModule(llvm::Module& M) override;
private:
    static char ID;
};
}

#endif /* YASSI_BRANCH_PASS_HPP */
