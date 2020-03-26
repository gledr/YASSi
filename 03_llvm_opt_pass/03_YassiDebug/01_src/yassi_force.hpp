#ifndef FOREST_FORCE_ASSERTION_PASS_HPP
#define FOREST_FORCE_ASSERTION_PASS_HPP

#ifdef FOREST_DEBUG_PASS
    #include "yassi_basepass.hpp"
#else 
    #include "../../00_GenericPasses/01_src/yassi_basepass.hpp"
#endif
    

namespace Yassi::OptPass::Debug {

class ForceAssertionPass : public llvm::ModulePass,  public virtual BasePass {
public:
    ForceAssertionPass();
// 
    virtual ~ForceAssertionPass();

    bool runOnModule(llvm::Module& M) override;

private:
    static char ID;
};
}

#endif /* FOREST_FORCE_ASSERTION_PASS_HPP */
