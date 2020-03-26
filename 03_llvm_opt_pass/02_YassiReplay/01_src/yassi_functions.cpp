#include "yassi_functions.hpp"

using namespace Yassi::OptPass::Replay;

char FunctionsPass::ID = 0;

FunctionsPass::FunctionsPass(): 
    ReplayBase(), llvm::ModulePass(FunctionsPass::ID) 
{

}

FunctionsPass::~FunctionsPass() 
{

}

bool FunctionsPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {

        std::string fn_name = this->demangle_fn_name(fun->getName().str());

        if(this->is_special_llvm_function(fn_name)){
            continue;
        }

        llvm::Function::arg_iterator arg_begin = fun->arg_begin();
        llvm::Function::arg_iterator arg_end   = fun->arg_end();

        std::stringstream function_operand_list;
        for(auto it = arg_begin; it != arg_end; it++ ) {
            function_operand_list << this->operandname(llvm::cast<llvm::Value>(it)) << ",";
        }
        std::string fn_oplist = function_operand_list.str();

        llvm::GlobalVariable* c1 = this->make_global_str(M, fn_name );
        llvm::GlobalVariable* c2 = this->make_global_str(M, fn_oplist);
        llvm::GlobalVariable* c3 = this->make_global_str(M, p_current_source_file);

        llvm::FunctionType* begin_fn_type = llvm::TypeBuilder<void(char*, char*, char*), false>::get(M.getContext());
        llvm::Function* begin_fn_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_BEGIN_FN, begin_fn_type));
        
        llvm::FunctionType* end_fn_type = llvm::TypeBuilder<void(void), false>::get(M.getContext());
        llvm::Function* end_fn_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(REPLAY_BACKEND_FN_END_FN, end_fn_type));
        
        llvm::Function::iterator begin = fun->begin();
        llvm::Function::iterator end   = fun->end();

        if(begin != end) {
            llvm::BasicBlock::iterator insertpos_begin = fun->begin()->begin();
            std::vector<llvm::Value*> params_begin;
            params_begin.push_back(this->pointerToArray(M,c1));
            params_begin.push_back(this->pointerToArray(M,c2));
            params_begin.push_back(this->pointerToArray(M,c3));
            llvm::CallInst::Create(begin_fn_fun, params_begin, "", llvm::cast<llvm::Instruction>(insertpos_begin));
            
            llvm::Function::iterator insertfn = fun->end(); insertfn--;
            llvm::BasicBlock::iterator insertpos_end = insertfn->end(); insertpos_end--;
            std::vector<llvm::Value*> params_end;
            llvm::CallInst::Create(end_fn_fun, params_end, "", llvm::cast<llvm::Instruction>(insertpos_end));
        }
    }
    return false;
}
