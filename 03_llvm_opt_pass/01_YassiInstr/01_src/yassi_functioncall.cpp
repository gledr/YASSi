/** 
 * @file yassi_functioncall.cpp
 * @brief Optimization Pass to handle function calls
 *
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2020 Johannes Kepler University
 * @author Sebastian Pointner
 * @author Pablo Gonzales de Aledo
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
#include "yassi_functioncall.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Types;

char FunctionCallPass::ID = 0;

FunctionCallPass::FunctionCallPass(): 
    InstrBase(),
    llvm::ModulePass(FunctionCallPass::ID) 
{
}

FunctionCallPass::~FunctionCallPass() 
{
}

bool FunctionCallPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        if(this->is_internal_yassi_function(fun->getName().str())){
            continue;
        }
        
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {

                if(llvm::isa<llvm::CallInst>(in)) {

                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst>(in);

                    bool hasname = in_c->getCalledFunction();

                    std::string fn_name;
                    if(hasname) {
                        fn_name = in_c->getCalledFunction()->getName().str();
                    } else {
                        llvm::Value* called_v = in_c->getCalledValue();
                        if( llvm::ConstantExpr::classof(called_v) ) {
                            llvm::ConstantExpr* called_e = llvm::cast<llvm::ConstantExpr>(called_v);
                            llvm::Function* called_f = llvm::cast<llvm::Function>(called_e->getOperand(0));
                            fn_name = called_f->getName().str();
                        } else {
                            fn_name = this->operandname(called_v);
                        }
                    }

                    std::string unmangled_fn_name = this->demangle_fn_name(fn_name);

                    if(!this->is_backend_symbolic_function(fn_name) && !this->is_special_llvm_function(fn_name)){
                        std::stringstream operand_list;
                        for (size_t i = 0; i < in_c->getNumOperands()-1; i++) {
                            std::string name = this->operandname( in_c->getArgOperand(i) );
                            operand_list << name << VARIABLE_SEPERATOR;
                        }

                        std::string oplist  = operand_list.str();

                        std::string ret_to = this->operandname(in_c);
                        
                        BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(in_c->getType()->getTypeID()), in_c->getType()->getPrimitiveSizeInBits());

                        llvm::GlobalVariable* c1 = this->make_global_str(M, unmangled_fn_name);
                        llvm::GlobalVariable* c2 = this->make_global_str(M, oplist);
                        llvm::GlobalVariable* c3 = this->make_global_str(M, ret_to);
                        llvm::GlobalVariable* c4 = this->make_global_str(M, type->get_type_identifier());
                        llvm::GlobalVariable* c6 = this->make_global_str(M, this->demangle_fn_name(fun->getName().str()));

                        llvm::FunctionType* call_instr_type = llvm::TypeBuilder<void(char*, char*, char*), false>::get(M.getContext());
                        llvm::Function* call_instr_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_CALL_INSTR, call_instr_type));
                         
                        llvm::FunctionType* call_instr_post_type = llvm::TypeBuilder<void(char*, char*, char*), false>::get(M.getContext());
                        llvm::Function* call_instr_post_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_CALL_POST, call_instr_post_type));

                        llvm::BasicBlock::iterator insertpos = in;

                        std::vector<llvm::Value*> params1;
                        params1.push_back(this->pointerToArray(M,c1));
                        params1.push_back(this->pointerToArray(M,c2));
                        params1.push_back(this->pointerToArray(M,c3));
                        llvm::CallInst::Create(call_instr_fun, params1, "", llvm::cast<llvm::Instruction>(insertpos));

                        insertpos++;
                        in++;

                        std::vector<llvm::Value*> params2;
                        params2.push_back(this->pointerToArray(M,c1));
                        params2.push_back(this->pointerToArray(M,c4));
                        params2.push_back(this->pointerToArray(M,c6));
                        llvm::CallInst::Create(call_instr_post_fun, params2, "", llvm::cast<llvm::Instruction>(insertpos));

                        in--;
                    }

                } else if(llvm::isa<llvm::ReturnInst>(in)) {
                    llvm::ReturnInst* in_r = llvm::cast<llvm::ReturnInst>(in);

                    std::string returnoperand;
                    if(!in_r->getReturnValue()) {
                        returnoperand = this->make_constant(VOIDTYPE, "null");
                    } else {
                        returnoperand = this->operandname( in_r->getReturnValue() );
                    }
                    llvm::GlobalVariable* c1 = this->make_global_str(M, returnoperand );

                    llvm::FunctionType* return_type = llvm::TypeBuilder<void(char*), false>::get(M.getContext());
                    llvm::Function* return_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_FN_RETURN, return_type));

                    llvm::BasicBlock::iterator insertpos = in;

                    std::vector<llvm::Value*> params;
                    params.push_back(this->pointerToArray(M,c1));
                    llvm::CallInst::Create(return_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
                }
            }
        }
    }
    return false;
}
