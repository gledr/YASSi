#include "yassi_debug_pass.hpp"

using namespace Yassi::OptPass::Debug;
using namespace Yassi::Utils;

char DebugAll::ID = 0;
static llvm::RegisterPass<DebugAll> DebugAll("debug_all", "Debug");

DebugAll::DebugAll(): 
    Yassi::OptPass::BasePass(), ModulePass(DebugAll::ID) 
{

}

bool DebugAll::runOnModule(llvm::Module &M) 
{
    p_verbose && std::cerr << BaseUtils::get_bash_string_blink_purple("Starting Debug Pass") << std::endl;
        { ForceAssertionPass     pass; p_verbose && std::cerr << "ChangeAssertions"     << std::endl; pass.runOnModule(M); }
        { SelectVariables        pass; p_verbose && std::cerr << "SelectVariables"      << std::endl; pass.runOnModule(M); }
    p_verbose && std::cerr << BaseUtils::get_bash_string_blink_purple("Debug Pass Finished") << std::endl << std::endl;;
    return false;
}
