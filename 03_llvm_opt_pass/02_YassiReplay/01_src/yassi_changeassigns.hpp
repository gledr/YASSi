#ifndef YASSI_CHANGEASSIGNS_PASS_HPP
#define YASSI_CHANGEASSIGNS_PASS_HPP

#include "yassi_replaybase.hpp"
    
namespace Yassi::OptPass::Replay {

class ChangeAssignsPass: public llvm::ModulePass,  public virtual ReplayBase {
public:
    ChangeAssignsPass();

    virtual ~ChangeAssignsPass();

    bool runOnModule(llvm::Module& M) override;

private:
    static char ID;

    std::map<std::string, std::string> load_names_from_pos();
};

}

#endif /* YASSI_CHANGEASSIGNS_PASS_HPP */
