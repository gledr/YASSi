#ifndef YASSI_REPLAYBASE_HPP
#define YASSI_REPLAYBASE_HPP

#ifdef YASSI_MEAS_PASS
    #include "yassi_basepass.hpp"
#else 
    #include "../../00_GenericPasses/01_src/yassi_basepass.hpp"
#endif

namespace Yassi::OptPass::Replay {

class ReplayBase :  public virtual Yassi::OptPass::BasePass {
protected:
    ReplayBase();
    
    virtual ~ReplayBase();
    
    static std::string const REPLAY_BACKEND_FN_BEGIN_SIM;
    static std::string const REPLAY_BACKEND_FN_END_SIM;
    
    static std::string const REPLAY_BACKEND_FN_BEGIN_BB;
    static std::string const REPLAY_BACKEND_FN_END_BB;
    
    static std::string const REPLAY_BACKEND_FN_BEGIN_FN;
    static std::string const REPLAY_BACKEND_FN_END_FN;
    
    static std::string const REPLAY_BACKEND_FN_BRANCH_COND;
    static std::string const REPLAY_BACKEND_FN_BRANCH_INCOND;

    static std::string const REPLAY_BACKEND_FN_VECTOR_CHAR;
    static std::string const REPLAY_BACKEND_FN_VECTOR_SHORT;
    static std::string const REPLAY_BACKEND_FN_VECTOR_INT;
    static std::string const REPLAY_BACKEND_FN_VECTOR_LONG;
    static std::string const REPLAY_BACKEND_FN_VECTOR_FLOAT;
    static std::string const REPLAY_BACKEND_FN_VECTOR_DOUBLE;
    
    static std::string const VERIFIER_NONDET_INT;
    static std::string const VERIFIER_NONDET_UINT;
    static std::string const VERIFIER_NONDET_CHAR;
    static std::string const VERIFIER_NONDET_BOOL;
    static std::string const VERIFIER_NONDET_LONG;
    static std::string const VERIFIER_NONDET_POINTER;
};

}

#endif /* YASSI_REPLAYBASE_HPP */
