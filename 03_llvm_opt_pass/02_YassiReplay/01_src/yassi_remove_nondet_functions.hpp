#ifndef YASSI_REMOVENONDET_PASS_HPP
#define YASSI_REMOVENONDET_PASS_HPP

#include "yassi_replaybase.hpp"

namespace Yassi::OptPass::Replay {

class RemoveNondetFunctionsPass : public llvm::ModulePass,  public virtual ReplayBase {
public:
    RemoveNondetFunctionsPass();

    ~RemoveNondetFunctionsPass();

    bool runOnModule(llvm::Module& M) override;

    static char ID;
private:
  
};

}

#endif /* YASSI_REMOVENONDET_PASS_HPP */
