#include "yassi_replaybase.hpp"

using namespace Yassi::OptPass::Replay;

std::string const ReplayBase::REPLAY_BACKEND_FN_BEGIN_BB        = "__REPLAY_begin_bb";
std::string const ReplayBase::REPLAY_BACKEND_FN_END_BB          = "__REPLAY_end_bb";

std::string const ReplayBase::REPLAY_BACKEND_FN_BEGIN_SIM       = "__REPLAY_begin_sim";
std::string const ReplayBase::REPLAY_BACKEND_FN_END_SIM         = "__REPLAY_end_sim";

std::string const ReplayBase::REPLAY_BACKEND_FN_BEGIN_FN        = "__REPLAY_begin_fn";
std::string const ReplayBase::REPLAY_BACKEND_FN_END_FN          = "__REPLAY_end_fn";

std::string const ReplayBase::REPLAY_BACKEND_FN_BRANCH_COND     = "__REPLAY_br_instr_cond";
std::string const ReplayBase::REPLAY_BACKEND_FN_BRANCH_INCOND   = "__REPLAY_br_instr_incond";

std::string const ReplayBase::REPLAY_BACKEND_FN_VECTOR_CHAR     = "__REPLAY_vector_char";
std::string const ReplayBase::REPLAY_BACKEND_FN_VECTOR_SHORT    = "__REPLAY_vector_short";
std::string const ReplayBase::REPLAY_BACKEND_FN_VECTOR_INT      = "__REPLAY_vector_int";
std::string const ReplayBase::REPLAY_BACKEND_FN_VECTOR_LONG     = "__REPLAY_vector_long";
std::string const ReplayBase::REPLAY_BACKEND_FN_VECTOR_FLOAT    = "__REPLAY_vector_float";
std::string const ReplayBase::REPLAY_BACKEND_FN_VECTOR_DOUBLE   = "__REPLAY_vector_double";

std::string const ReplayBase::VERIFIER_NONDET_INT               = "__VERIFIER_nondet_int";
std::string const ReplayBase::VERIFIER_NONDET_UINT              = "__VERIFIER_nondet_uint";
std::string const ReplayBase::VERIFIER_NONDET_CHAR              = "__VERIFIER_nondet_char";
std::string const ReplayBase::VERIFIER_NONDET_BOOL              = "__VERIFIER_nondet_bool";
std::string const ReplayBase::VERIFIER_NONDET_LONG              = "__VERIFIER_nondet_long";
std::string const ReplayBase::VERIFIER_NONDET_POINTER           = "__VERIFIER_nondet_pointer";

ReplayBase::ReplayBase():
    Yassi::OptPass::BasePass()
{
}

ReplayBase::~ReplayBase()
{
}

