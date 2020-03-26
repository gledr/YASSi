#ifndef YASSI_CLEANPHI_PASS_HPP
#define YASSI_CLEANPHI_PASS_HPP

#include "yassi_instrbase.hpp"

namespace Yassi::OptPass::Execute {

class CleanPhiPass : public llvm::ModulePass,  public virtual InstrBase {
public:
    CleanPhiPass();

    ~CleanPhiPass();

    bool runOnModule(llvm::Module& M) override;

private:
    static char ID;
};

}

#endif /* YASSI_CLEANPHI_PASS_HPP */
