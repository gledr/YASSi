/** 
 * @file yassi_beginend.cpp
 * @brief Optimization Pass to Handle LLVM IR's Basic Blocks
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
#include "yassi_beginend.hpp"

using namespace Yassi::OptPass::Execute;


char BeginEndPass::ID = 0;

/**
 * @brief Constructor
 * 
 */
BeginEndPass::BeginEndPass():
    InstrBase(),
    llvm::ModulePass(BeginEndPass::ID)
{
}

/**
 * @brief Destructor
 */
BeginEndPass::~BeginEndPass()
{
}

/**
 * @brief Overriden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool BeginEndPass::runOnModule(llvm::Module& M)
{
    if(!M.getFunction("main")) {
        // Main Function not detected in this file!
        return false;
    }

    llvm::BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();

    llvm::FunctionType* begin_sim_type =
        llvm::TypeBuilder<void(char*), false>::get(M.getContext());
    llvm::Function* begin_sim_fun =
        llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_BEGIN_SIM, begin_sim_type));

    llvm::FunctionType* end_sim_type =
        llvm::TypeBuilder<void(void), false>::get(M.getContext());
    llvm::Function* end_sim_fun =
        llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_END_SIM, end_sim_type));

    llvm::GlobalVariable* c1 = this->make_global_str(M, p_current_source_file);

    std::vector<llvm::Value*> params_begin;
    params_begin.push_back(this->pointerToArray(M,c1));
    llvm::CallInst::Create(begin_sim_fun,
                           params_begin,
                           "",
                           llvm::cast<llvm::Instruction>(insertpos));

    llvm::BasicBlock::iterator insertpos_b =
        return_bb(llvm::cast<llvm::Function>(M.getFunction("main")))->end();
    insertpos_b--;

    std::vector<llvm::Value*> params_end;
    llvm::CallInst::Create(end_sim_fun,
                           params_end,
                           "",
                           llvm::cast<llvm::Instruction>(insertpos_b));

    return false;
}

/**
 * @brief Find the Basic Block of a Function's Return Instruction
 * 
 * @param function Funtion to Check
 * @return llvm::BasicBlock*
 */
llvm::BasicBlock* BeginEndPass::return_bb(llvm::Function* function)
{
    for(auto bb = function->begin(), block_end = function->end(); bb != block_end; ++bb) {
        for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
            if(llvm::isa<llvm::ReturnInst>(in)) {
                return llvm::cast<llvm::BasicBlock>(bb);
            }
        }
    }
    assert(0 && "No return bb");
}
