#include "yassi_remove_nondet_functions.hpp"

using namespace Yassi::OptPass::Replay;

char RemoveNondetFunctionsPass::ID = 0;
static llvm::RegisterPass<RemoveNondetFunctionsPass> RemoveNondetFunctionsPass("rm_nondet", "Remove Non-Deterministic Verification Functions");

RemoveNondetFunctionsPass::RemoveNondetFunctionsPass(): 
    ReplayBase(), llvm::ModulePass(RemoveNondetFunctionsPass::ID) 
{

}

RemoveNondetFunctionsPass::~RemoveNondetFunctionsPass() 
{

}

bool RemoveNondetFunctionsPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        std::vector<llvm::CallInst*> instr_to_rm;

        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::CallInst>(in)){
                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst>(in);

                    bool hasname = in_c->getCalledFunction();
                 
                    if(hasname){
                        std::string fn_name = in_c->getCalledFunction()->getName().str();
                        std::string demangled_fn_name = this->demangle_fn_name(fn_name);
                        if(demangled_fn_name == VERIFIER_NONDET_INT)        instr_to_rm.push_back(in_c);
                        if(demangled_fn_name == VERIFIER_NONDET_CHAR)       instr_to_rm.push_back(in_c);
                        if(demangled_fn_name == VERIFIER_NONDET_UINT)       instr_to_rm.push_back(in_c);
                        if(demangled_fn_name == VERIFIER_NONDET_BOOL)       instr_to_rm.push_back(in_c);
                        if(demangled_fn_name == VERIFIER_NONDET_LONG)       instr_to_rm.push_back(in_c);
                        if(demangled_fn_name == VERIFIER_NONDET_POINTER)    instr_to_rm.push_back(in_c);
                    }
                }
            }
        }
    
        for(auto instr : instr_to_rm){
            llvm::ConstantInt* zero = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef("0"), 10));
            std::vector<llvm::Value*> indices; 
            indices.push_back(zero);
            
            llvm::AllocaInst* ai = new llvm::AllocaInst(instr->getType(), 0, instr->getName().str(), instr);
            llvm::GetElementPtrInst* getelement = llvm::GetElementPtrInst::Create(NULL, ai, indices, "pointer", instr);
            llvm::LoadInst* load = new llvm::LoadInst(getelement, "load", false, instr);

            for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
                for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                    if(in->getNumOperands() > 0 && in->getOperand(0) == instr) in->setOperand(0, load);
                    if(in->getNumOperands() > 1 && in->getOperand(1) == instr) in->setOperand(1, load);
                }
            }

            if(!(instr)->getNumUses()){
                    instr->eraseFromParent();
            } else {
                llvm::Instruction* allocainst = new llvm::AllocaInst(instr->getType(), 0, "");
                llvm::Instruction* loadinst   = new llvm::LoadInst(allocainst, "");
                llvm::BasicBlock::iterator insertpos(instr);
        
                allocainst->insertBefore(instr);
                instr->getParent()->replaceAllUsesWith(loadinst);
            }
        }
    }
    return false;
}
