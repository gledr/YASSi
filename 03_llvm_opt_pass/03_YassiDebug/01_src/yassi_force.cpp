#include "yassi_force.hpp"

using namespace Yassi::OptPass::Debug;

char ForceAssertionPass::ID = 0;

ForceAssertionPass::ForceAssertionPass(): 
    BasePass(), ForceAssertionPass::ModulePass(ForceAssertionPass::ID) 
{

}

ForceAssertionPass::~ForceAssertionPass() 
{

}

bool ForceAssertionPass::runOnModule(llvm::Module& M) 
{
    std::vector<llvm::Instruction*> instr_to_rm;

    for ( auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun ) {
        for ( auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb ) {
            for ( auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in ) {
                if (llvm::isa<llvm::CallInst>(in)) {

                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst> (in);

                    bool hasname = in_c->getCalledFunction();
                    std::string fn_name;
                    if ( hasname ) {
                        fn_name = this->demangle_fn_name(in_c->getCalledFunction()->getName().str());
                        if (fn_name.find(BACKEND_FN_VERIFIER_ASSERT) != std::string::npos) {

                            instr_to_rm.push_back (llvm::cast<llvm::Instruction>(in));

                            std::string nameass = this->operandname (in_c->getArgOperand (0));
                            std::string position = this->line_number_of_instruction(*in);

                            llvm::GlobalVariable* c1 = this->make_global_str(M, nameass);
                            llvm::GlobalVariable* c2 = this->make_global_str(M, position);

                            llvm::FunctionType* fun_type = llvm::TypeBuilder<void(char*, char*), false>::get(M.getContext());
                            llvm::Function* fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(BACKEND_FN_FORCE_ASSERTION, fun_type));

                            llvm::BasicBlock::iterator insertpos = in;
                            insertpos++;

                            std::vector<llvm::Value*> params;
                            params.push_back(this->pointerToArray (M,c1));
                            params.push_back(this->pointerToArray (M,c2));

                            llvm::CallInst::Create (fun , params, "", llvm::cast<llvm::Instruction>(insertpos) );
                        }
                    }
                }
            }
        }
    }

    for (auto it: instr_to_rm) {
        it->eraseFromParent();
    }
    
    return false;
}
