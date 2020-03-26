#ifndef FOREST_SELECTVARIABLES_HPP
#define FOREST_SELECTVARIABLES_HPP

#ifdef FOREST_DEBUG_PASS
    #include "yassi_basepass.hpp"
#else 
    #include "../00_GenericPasses/01_src/yassi_basepass.hpp"
#endif

namespace Yassi::OptPass::Debug {
  /*
   * This pass is needed to extract the information of used binary statements in loop latches.
   * Since we are depended on LoopInfo, we must use a FunctionPass for that - we can not integrate
   * that into our module passes. 
   * We have to call this pass using opt -load *-so -loop_latch_info before invoking the insert_select_variables
   * pass since we can not call it automatically from a Module Pass. 
   */
class LoopLatchParser : public llvm::FunctionPass, public virtual BasePass {
public:
    static char ID;
    LoopLatchParser();
    
    virtual ~LoopLatchParser();
    
    // Tell LLVM that we are dependent on LoopInfo
    void getAnalysisUsage (llvm::AnalysisUsage & AU) const;

    virtual bool runOnFunction (llvm::Function &F);

  private: 
    void AnalyseLoop (llvm::Loop * L, size_t nesting);
};


struct ReplaceAfter {
  llvm::Instruction* instr_to_replace;
  llvm::Instruction* replace_by;
};

class SelectVariables: public llvm::ModulePass, public virtual BasePass {
public:

    SelectVariables();
  
    virtual ~SelectVariables();

    virtual bool runOnModule(llvm::Module &M);

    bool blacklisted_instruction (llvm::Instruction const & ins);

    void dump_blacklisted_lines ();
    
    static char ID;
    
private:
    std::vector<std::string> p_blacklisted_lines;

};

}

#endif /* FOREST_SELECTVARIABLES_HPP */
