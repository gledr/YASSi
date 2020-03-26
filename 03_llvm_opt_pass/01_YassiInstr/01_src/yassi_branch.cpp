/** 
 * @file yassi_branch.cpp
 * @brief Optimization Pass to Handle LLVM's Branch Instructions
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
#include "yassi_branch.hpp"

using namespace Yassi::OptPass::Execute;

char BranchPass::ID = 0;

BranchPass::BranchPass():
    InstrBase(),
    llvm::ModulePass(BranchPass::ID)
{
}

BranchPass::~BranchPass()
{
}

bool BranchPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {


                if(llvm::isa<llvm::BranchInst>(in)) {
                    llvm::BranchInst* in_b = llvm::cast<llvm::BranchInst>(in);

                    if(in_b->isConditional()) {
                        std::string joints_s;
                        std::string nameop1 = this->operandname(in->getOperand(0) );
                      
                        llvm::GlobalVariable* c1 = this->make_global_str(M, nameop1);
                        llvm::GlobalVariable* c2 = this->make_global_str(M, joints_s);
                    
                        std::vector<llvm::Type *> args (2,
                                                        llvm::Type::getInt8PtrTy(M.getContext()));
                        
                        llvm::FunctionType *cond_branch_type =
                            llvm::FunctionType::get(llvm::Type::getInt1Ty(M.getContext()), args, false);
                        llvm::Function* cond_branch_fun =
                            llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_BRANCH_COND, cond_branch_type));
                        
                        llvm::BasicBlock::iterator insertpos = in;

                        std::vector<llvm::Value*> params;
                        params.push_back(this->pointerToArray(M,c1));
                        params.push_back(this->pointerToArray(M,c2));

                        llvm::CallInst* ci = 
                            llvm::CallInst::Create(cond_branch_fun,
                                                   params,
                                                   "",
                                                   llvm::cast<llvm::Instruction>(insertpos));
                        in_b->setCondition(ci);
                      
                    } else {
                        llvm::FunctionType* incond_branch_type =
                            llvm::TypeBuilder<void(void), false>::get(M.getContext());
                        llvm::Function* incond_branch_fun =
                            llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_BRANCH_INCOND, incond_branch_type));
                        
                        llvm::BasicBlock::iterator insertpos = in;

                        std::vector<llvm::Value*> params;
                        llvm::CallInst::Create(incond_branch_fun,
                                               params,
                                               "",
                                               llvm::cast<llvm::Instruction>(insertpos));
                    }
                }
            }
        }
    }
    return false;
}
