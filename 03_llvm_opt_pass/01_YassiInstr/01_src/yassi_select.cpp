/** 
 * @file yassi_select.cpp
 * @brief Optimization Pass to Handle LLVM IR's Select Operation
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
#include "yassi_select.hpp"

using namespace Yassi::OptPass::Execute;

char SelectPass::ID = 0;

/**
 * @brief Constructor
 */
SelectPass::SelectPass():
    InstrBase(),
    llvm::ModulePass(SelectPass::ID) 
{
}

/**
 * @brief Destructor
 */
SelectPass::~SelectPass()
{
}

/**
 * @brief Overriden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool SelectPass::runOnModule(llvm::Module& M)
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {

                if(llvm::isa<llvm::SelectInst>(in) ) {;
                    std::string nameres = this->make_register_name(in->getName().str());
                    std::string nameop1 = this->operandname(in->getOperand(0));
                    std::string nameop2 = this->operandname(in->getOperand(1));
                    std::string nameop3 = this->operandname(in->getOperand(2));                

                    llvm::GlobalVariable* c1 = this->make_global_str(M, nameres);
                    llvm::GlobalVariable* c2 = this->make_global_str(M, nameop1);
                    llvm::GlobalVariable* c3 = this->make_global_str(M, nameop2);
                    llvm::GlobalVariable* c4 = this->make_global_str(M, nameop3);

                    llvm::FunctionType* sel_op_type = llvm::TypeBuilder<void(char*, char*, char*, char*), false>::get(M.getContext());
                    llvm::Function* sel_op_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_SELECT, sel_op_type));

                    llvm::BasicBlock::iterator insertpos = in;
                    insertpos++;

                    std::vector<llvm::Value*> params;
                    params.push_back(this->pointerToArray(M,c1));
                    params.push_back(this->pointerToArray(M,c2));
                    params.push_back(this->pointerToArray(M,c3));
                    params.push_back(this->pointerToArray(M,c4));
                    llvm::CallInst::Create(sel_op_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
                }
            }
        }
    }
    return false;
}
