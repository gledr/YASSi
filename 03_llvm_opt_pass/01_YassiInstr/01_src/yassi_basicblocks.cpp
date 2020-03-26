/** 
 * @file yassi_basicblocks.cpp
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
#include "yassi_basicblocks.hpp"

using namespace Yassi::OptPass::Execute;


char BasicBlocksPass::ID = 0;

/**
 * @brief Constructor
 */
BasicBlocksPass::BasicBlocksPass():
    InstrBase(),
    llvm::ModulePass(BasicBlocksPass::ID)
{
}

/**
 * @brief Destructor
 */
BasicBlocksPass::~BasicBlocksPass()
{
}

/**
 * @brief Overridden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool BasicBlocksPass::runOnModule(llvm::Module& M)
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {

            if(this->is_internal_yassi_function(fun->getName().str())){
                continue;
            }

            bool phi_node = false;
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                // @ sebastian: If there is a phi node in the block
                //              the begin_bb call must no be on top!
                if (llvm::isa<llvm::PHINode>(in)) {
                    phi_node = 1;
                    break;
                }
            }

            std::string begin_bb = "begin_" + bb->getName().str();
            std::string end_bb = "end_" + bb->getName().str();
            std::string fn_name = this->demangle_fn_name(fun->getName().str());

            p_db->insert_basic_block(this->p_current_source_file, fn_name, begin_bb);
            p_db->insert_basic_block(this->p_current_source_file, fn_name, end_bb);

            llvm::GlobalVariable* c1 = this->make_global_str(M,begin_bb);
            llvm::GlobalVariable* c2 = this->make_global_str(M,end_bb);

            llvm::FunctionType* begin_bb_type = llvm::TypeBuilder<void(char*), false>::get(M.getContext());
            llvm::Function* begin_bb_fun =
                llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_BEGIN_BB, begin_bb_type));

            llvm::FunctionType* end_bb_type =
                llvm::TypeBuilder<void(char*), false>::get(M.getContext());
            llvm::Function* end_bb_fun =
                llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_END_BB, end_bb_type));

            llvm::BasicBlock::iterator insertpos_begin_fn = bb->begin();
            if (phi_node) {
                insertpos_begin_fn++;
            }
            std::vector<llvm::Value*> params_begin_fn;
            params_begin_fn.push_back(this->pointerToArray(M,c1));
            llvm::CallInst::Create(begin_bb_fun,
                                   params_begin_fn,
                                   "",
                                   llvm::cast<llvm::Instruction>(insertpos_begin_fn));

            llvm::BasicBlock::iterator insertpos_end_fn = bb->end();
            insertpos_end_fn--;

            std::vector<llvm::Value*> params_end_fn;
            params_end_fn.push_back(this->pointerToArray(M,c2));
            llvm::CallInst::Create(end_bb_fun,
                                   params_end_fn,
                                   "",
                                   llvm::cast<llvm::Instruction>(insertpos_end_fn));
        }
    }
    return false;
}
