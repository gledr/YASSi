#ifndef YASSI_REPLAY_PASS_HPP
#define YASSI_REPLAY_PASS_HPP

#ifdef YASSI_MEAS_PASS
    #include "yassi_database.hpp"
    #include "yassi_basicblocks.hpp"
    #include "yassi_functions.hpp"
    #include "yassi_branch.hpp"
    #include "yassi_changemainmeasure.hpp"
    #include "yassi_changeassigns.hpp"
    #include "yassi_beginend.hpp"
    #include "yassi_fillnames.hpp"
    #include "yassi_basepass.hpp"
    #include "yassi_removeforcefree.hpp"
    #include "yassi_removeprintf.hpp"
    #include "yassi_remove_nondet_functions.hpp"
#else
    #include "../../04_utils/01_src/yassi_database.hpp"
    #include "../00_GenericPasses/01_src/yassi_basepass.hpp"
    #include "../02_YassiReplay/01_src/yassi_basicblocks.hpp"
    #include "../00_GenericPasses/01_src/yassi_functions.hpp"
    #include "../00_GenericPasses/01_src/yassi_branch.hpp"
    #include "../00_GenericPasses/01_src/yassi_fillnames.hpp"
    #include "../00_GenericPasses/01_src/yassi_removeprrintf.hpp"
    #include "../00_GenericPasses/01_src/yassi_remove_nondet_functions.hpp"
    #include "../02_YassiReplay/01_src/yassi_changemainmeasure.hpp"
    #include "../02_YassiReplay/01_src/yassi_changeassigns.hpp"
    #include "../02_YassiReplay/01_src/yassi_beginend.hpp"
    #include "../02_YassiReplay/01_src/yassi_removeforcefree.hpp"
#endif

namespace Yassi::OptPass::Replay {

class ReplayAll: public llvm::ModulePass, public virtual Yassi::OptPass::BasePass {
public:
	ReplayAll();

	virtual bool runOnModule(llvm::Module &M) override;
	
	static char ID;
};

}

#endif /* YASSI_REPLAY_PASS_HPP */
