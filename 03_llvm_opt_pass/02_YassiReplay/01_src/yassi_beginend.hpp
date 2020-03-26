#ifndef YASSI_BEGINEND_PASS_HPP
#define YASSI_BEGINEND_PASS_HPP

#include "yassi_replaybase.hpp"

namespace Yassi::OptPass::Replay {

class BeginEndPass: public llvm::ModulePass, public virtual ReplayBase {
public:
    BeginEndPass();

    virtual ~BeginEndPass();

    bool runOnModule(llvm::Module& M) override;

private:
    static char ID;
};

}

#endif /* YASSI_BEGINEND_PASS_HPP */
