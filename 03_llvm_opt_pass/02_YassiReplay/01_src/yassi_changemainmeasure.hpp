#ifndef YASSI_CHANGEMAINMEASURE_PASS_HPP
#define YASSI_CHANGEMAINMEASURE_PASS_HPP

#include "yassi_replaybase.hpp"
    
namespace Yassi::OptPass::Replay {

class ChangeMainMeasurePass : public llvm::ModulePass,  public virtual ReplayBase {
public:
    ChangeMainMeasurePass();

    ~ChangeMainMeasurePass();

    bool runOnModule(llvm::Module& M) override;

private:
    static char ID;
    std::vector<Yassi::Utils::VariableInfo> p_test_vector_variables;

    void insert_main_function_calling(llvm::Value* func_test, llvm::Module & M, size_t const iterations);
};

}

#endif /* YASSI_CHANGEMAINMEASURE_PASS_HPP */
