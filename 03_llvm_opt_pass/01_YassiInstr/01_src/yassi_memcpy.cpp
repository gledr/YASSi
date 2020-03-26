/** 
 * @file yassi_memcpy.cpp
 * @brief Optimization Pass for Memory Copy
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
#include "yassi_memcpy.hpp"

using namespace Yassi::OptPass::Execute;


char MemcpyPass::ID = 0;

MemcpyPass::MemcpyPass():
    InstrBase(), llvm::ModulePass(MemcpyPass::ID)
{
}

MemcpyPass::~MemcpyPass() 
{
}

bool MemcpyPass::runOnModule(llvm::Module& M) 
{
    std::vector<llvm::Instruction*> instr_to_rm;

    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
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

                        if(! llvm::ConstantExpr::classof(called_v)) continue;

                        llvm::ConstantExpr* called_e = llvm::cast<llvm::ConstantExpr>(called_v);
                        llvm::Function* called_f = llvm::cast<llvm::Function>(called_e->getOperand(0));

                        fn_name = called_f->getName().str();
                    }

                    if(fn_name.substr(0,11) == "llvm.memcpy") {

                        instr_to_rm.push_back(llvm::cast<llvm::Instruction>(in));

                        std::stringstream operand_list;
                        for (size_t i = 0; i < in_c->getNumOperands()-1; i++) {
                            std::string name = this->operandname( in_c->getArgOperand(i) );
                            operand_list << name << ",";
                        }

                        std::string op2;
                        llvm::ConstantExpr* op1_ce = llvm::dyn_cast<llvm::ConstantExpr>(in_c->getArgOperand(1));
                        if(op1_ce) {
                            op2 = this->make_register_name(op1_ce->getOperand(0)->getName().str());
                        } else {
                            op2 = this->make_register_name(in_c->getArgOperand(1)->getName().str());
                        }

                        std::string op1 = this->operandname(in_c->getArgOperand(0));
                        std::string op3 = this->operandname(in_c->getArgOperand(2));
                        std::string op4 = this->operandname(in_c->getArgOperand(3));
                        std::string op5 = this->operandname(in_c->getArgOperand(4));

                        llvm::GlobalVariable* c1 = this->make_global_str(M, op1 );
                        llvm::GlobalVariable* c2 = this->make_global_str(M, op2 );
                        llvm::GlobalVariable* c3 = this->make_global_str(M, op3 );
                        llvm::GlobalVariable* c4 = this->make_global_str(M, op4 );
                        llvm::GlobalVariable* c5 = this->make_global_str(M, op5 );

                        llvm::FunctionType * memcpy_op_type = llvm::TypeBuilder<void(char*, char*, char*, char*, char*), false>::get(M.getContext());
                        llvm::Function* memcpy_op_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_MEMCPY, memcpy_op_type));
                        
                        llvm::BasicBlock::iterator insertpos = in;

                        std::vector<llvm::Value*> params;
                        params.push_back(this->pointerToArray(M,c1));
                        params.push_back(this->pointerToArray(M,c2));
                        params.push_back(this->pointerToArray(M,c3));
                        params.push_back(this->pointerToArray(M,c4));
                        params.push_back(this->pointerToArray(M,c5));
                        llvm::CallInst::Create(memcpy_op_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
                    }
                }
            }
        }
    }

    for(auto it: instr_to_rm) {
        it->eraseFromParent();
    }

    return false;
}
