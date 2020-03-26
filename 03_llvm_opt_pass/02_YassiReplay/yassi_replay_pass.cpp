#include "yassi_replay_pass.hpp"

using namespace Yassi::OptPass::Replay;
using namespace Yassi::Utils;

char ReplayAll::ID = 0;
static llvm::RegisterPass<ReplayAll> ReplayAll("replay_all", "Instrument all operations");

ReplayAll::ReplayAll(): 
    Yassi::OptPass::BasePass(), ModulePass(ReplayAll::ID) 
{

}

bool ReplayAll::runOnModule(llvm::Module &M) 
{
    p_verbose && std::cerr << BaseUtils::get_bash_string_blink_purple("Starting Measurement Pass") << std::endl;
        { FillNamesPass                 pass; p_verbose && std::cerr << "FillNamesPass"   << std::endl; pass.runOnModule(M); }
        { RemovePrintfPass              pass; p_verbose && std::cerr << "RemovePrintf"    << std::endl; pass.runOnModule(M); }
        { RemoveNondetFunctionsPass     pass; p_verbose && std::cerr << "RemoveNonDet"    << std::endl; pass.runOnModule(M); }
        { RemoveForceFreePass           pass; p_verbose && std::cerr << "RemoveForceFree" << std::endl; pass.runOnModule(M); }
        { BasicBlocksPass               pass; p_verbose && std::cerr << "BbMarks"         << std::endl; pass.runOnModule(M); }
        { FunctionsPass                 pass; p_verbose && std::cerr << "Functions"       << std::endl; pass.runOnModule(M); }
        { BranchPass                    pass; p_verbose && std::cerr << "BrInstr"         << std::endl; pass.runOnModule(M); }
        { ChangeMainMeasurePass         pass; p_verbose && std::cerr << "ChangeMain"      << std::endl; pass.runOnModule(M); }
        { ChangeAssignsPass             pass; p_verbose && std::cerr << "ChangeAssigns"   << std::endl; pass.runOnModule(M); }
        { BeginEndPass                  pass; p_verbose && std::cerr << "BeginEnd"        << std::endl; pass.runOnModule(M); }
    p_verbose && std::cerr << BaseUtils::get_bash_string_blink_purple("Measurement Pass Finished") << std::endl;
    return false;
}
