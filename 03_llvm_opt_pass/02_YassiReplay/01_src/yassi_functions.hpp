#ifndef YASSI_FUNCTIONS_PASS_HPP
#define YASSI_FUNCTIONS_PASS_HPP

#include "yassi_replaybase.hpp"

namespace Yassi::OptPass::Replay {

class FunctionsPass : public llvm::ModulePass, public virtual ReplayBase {
public:
    FunctionsPass();

    virtual ~FunctionsPass();

    bool runOnModule(llvm::Module & M) override;

private:
    static char ID; 
};

}

#endif /* YASSI_FUNCTIONS_PASS_HPP */
