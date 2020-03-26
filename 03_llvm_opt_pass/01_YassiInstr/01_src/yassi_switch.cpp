/**
 * @file yassi_switch.cpp
 * @brief Optimization Pass to Extract Switch Targets from LLVM's Switch Function
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
#include "yassi_switch.hpp"

using namespace Yassi::OptPass::Execute;


char SwitchPass::ID = 0;

/**
 * @brief Constructor
 */
SwitchPass::SwitchPass():
    InstrBase(),
    llvm::ModulePass(SwitchPass::ID)
{
}

/**
 * @brief Destructor
 */
SwitchPass::~SwitchPass()
{
}

/**
 * @brief Overriden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool SwitchPass::runOnModule(llvm::Module& M)
{
    std::vector<llvm::Instruction*> to_rm;

    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::SwitchInst>(in)) {

                    llvm::SwitchInst* in_s = llvm::cast<llvm::SwitchInst>(in);
                    llvm::BasicBlock* def = llvm::cast<llvm::BasicBlock>(in_s->getOperand(1));

                    to_rm.push_back(llvm::cast<llvm::Instruction>(in));

                    llvm::Value* reg = in_s->getOperand(0);

                    std::vector<llvm::BasicBlock*> bb_orig_v;
                    std::vector<llvm::BasicBlock*> bb_created_v;
                    std::vector<llvm::Value*> values_v;
                    
                    for (size_t i = 0; i < (in_s->getNumOperands()-2)/2; i++) {
                        llvm::BasicBlock* bb_orig    = llvm::cast<llvm::BasicBlock>(in_s->getOperand(2*i+3));
                        llvm::Value*      value      = in_s->getOperand(2*i+2);
                        llvm::BasicBlock* bb_created = llvm::BasicBlock::Create(M.getContext(), "bb_sw", llvm::cast<llvm::Function>(fun), 0);

                        bb_orig_v.push_back(bb_orig);
                        bb_created_v.push_back(bb_created);
                        values_v.push_back(value);
                    }

                    llvm::BranchInst::Create(llvm::cast<llvm::BasicBlock>(bb_created_v[0]), llvm::cast<llvm::BasicBlock>(bb));

                    for (size_t i = 0; i < bb_orig_v.size(); i++) {
                        llvm::Instruction* icmp   = new llvm::ICmpInst(*(bb_created_v[i]), llvm::ICmpInst::ICMP_EQ, reg, values_v[i], "" );

                        if(i==bb_orig_v.size()-1)
                            llvm::BranchInst::Create(bb_orig_v[i], def, icmp, bb_created_v[i]);
                        else
                            llvm::BranchInst::Create(bb_orig_v[i], bb_created_v[i+1], icmp, bb_created_v[i]);
                    }
                }
            }
        }
    }

    for(auto it : to_rm) {
        it->eraseFromParent();
    }

    return false;
}
