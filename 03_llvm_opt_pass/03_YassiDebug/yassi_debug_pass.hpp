#ifndef FOREST_DEBUG_PASS_HPP
#define FOREST_DEBUG_PASS_HPP

#ifdef FOREST_DEBUG_PASS
    #include "yassi_basepass.hpp"
    #include "yassi_force.hpp"
    #include "yassi_selectvariables.hpp"
#else
    #include "../00_GenericPasses/01_src/yassi_basepass.hpp"
    #include "01_src/yassi_force.hpp"
    #include "01_src/yassi_selectvariables.hpp"
#endif

namespace Yassi::OptPass::Debug {

class DebugAll: public llvm::ModulePass, public virtual Yassi::OptPass::BasePass {
public:
	DebugAll();

	virtual bool runOnModule(llvm::Module &M) override;
	
	static char ID;
};

}

#endif /* FOREST_DEBUG_PASS_HPP */
