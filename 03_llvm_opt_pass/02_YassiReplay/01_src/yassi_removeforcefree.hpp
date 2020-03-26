#ifndef YASSI_REMOVEFORCEFREE_PASS_HPP
#define YASSI_REMOVEFORCEFREE_PASS_HPP

#include "yassi_replaybase.hpp"

namespace Yassi::OptPass::Replay {
    
class RemoveForceFreePass : public llvm::ModulePass, public virtual ReplayBase {
public:
    RemoveForceFreePass();
    
    virtual ~RemoveForceFreePass();
    
    bool runOnModule(llvm::Module & M) override;
    
private:
    static char ID;
};

}

#endif /* YASSI_REMOVEFORCEFREE_PASS_HPP */
