/** 
 * @file yassi_alloca.cpp
 * @brief Optimization Pass to Handle LLVM IR's Alloca Operation
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
#include "yassi_alloca.hpp"

using namespace Yassi::OptPass::Execute;


char AllocaPass::ID = 0;

/**
 * @brief Constructor
 */

AllocaPass::AllocaPass():
    InstrBase(),
    llvm::ModulePass(ID)
{
}

/**
 * @brief Destructor
 */
AllocaPass::~AllocaPass()
{
}

/**
 * @brief Overriden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool AllocaPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::AllocaInst>(in)) {
                    llvm::AllocaInst* in_a = llvm::cast<llvm::AllocaInst>(in);

                    if(in_a->getName().find("alloca pointer") == 0){
                        continue;
                    }
                    
                    std::string nameres = this->make_register_name(in->getName().str());
                    std::string subtype = this->get_flattened_types(in_a->getAllocatedType());

                    llvm::GlobalVariable* c1 = this->make_global_str(M, nameres);
                    llvm::GlobalVariable* c2 = this->make_global_str(M, subtype);

                    llvm::FunctionType* alloca_op_type =
                        llvm::TypeBuilder<void(char*, char*), false>::get(M.getContext());
                    llvm::Function* alloca_op_fun =
                        llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_ALLOCA, alloca_op_type));

                    llvm::BasicBlock::iterator insertpos = in;
                    insertpos++;

                    std::vector<llvm::Value*> params;
                    params.push_back(this->pointerToArray(M,c1));
                    params.push_back(this->pointerToArray(M,c2));
                    llvm::CallInst::Create(alloca_op_fun,
                                           params,
                                           "",
                                           llvm::cast<llvm::Instruction>(insertpos));
                }
            }
        }
    }
    return false;
}
