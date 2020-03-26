/** 
 * @file yassi_separatecastinstr.cpp
 * @brief Optimization Pass to Extract Embedded Get ElementPointer Instructions from Function Calls
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
#include "yassi_seperategeteleptr.hpp"

using namespace Yassi::OptPass::Execute;

char SeperateGetElePtrPass::ID = 0;

/**
 * @brief Constructor
 */
SeperateGetElePtrPass::SeperateGetElePtrPass():
    InstrBase(),
    llvm::ModulePass(SeperateGetElePtrPass::ID)
{
}

/**
 * @brief Destructor
 */
SeperateGetElePtrPass::~SeperateGetElePtrPass()
{
}

/**
 * @brief Overriden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool SeperateGetElePtrPass::runOnModule(llvm::Module& M)
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::LoadInst>(in)) {
                    llvm::GEPOperator* gepop = llvm::dyn_cast<llvm::GEPOperator>(in->getOperand(0));

                    bool is_gepop;
                    is_gepop = llvm::dyn_cast<llvm::GEPOperator>(in->getOperand(0)) != NULL;
                    is_gepop = is_gepop && llvm::dyn_cast<llvm::GetElementPtrInst>(in->getOperand(0)) == NULL;

                    if(is_gepop) {
                        llvm::Value* pointer = gepop->getPointerOperand();
                        llvm::User::op_iterator idxbegin = gepop->idx_begin();
                        llvm::User::op_iterator idxend   = gepop->idx_end();
                        std::vector<llvm::Value*> indices(idxbegin, idxend);

                        llvm::GetElementPtrInst* getelement = llvm::GetElementPtrInst::Create(NULL, pointer, indices, "pointer", llvm::cast<llvm::Instruction>(in));

                        in->setOperand(0,getelement);
                    }
                } else if(llvm::isa<llvm::StoreInst>(in)) {
                    for (size_t i = 0; i < 2; i++) {

                        llvm::GEPOperator* gepop = llvm::dyn_cast<llvm::GEPOperator>(in->getOperand(i));

                        bool is_gepop;
                        is_gepop = llvm::dyn_cast<llvm::GEPOperator>(in->getOperand(i)) != NULL;
                        is_gepop = is_gepop && llvm::dyn_cast<llvm::GetElementPtrInst>(in->getOperand(i)) == NULL;

                        if(is_gepop) {
                            llvm::Value* pointer = gepop->getPointerOperand();
                            llvm::User::op_iterator idxbegin = gepop->idx_begin();
                            llvm::User::op_iterator idxend   = gepop->idx_end();
                            std::vector<llvm::Value*> indices(idxbegin, idxend);

                            llvm::GetElementPtrInst* getelement = llvm::GetElementPtrInst::Create(NULL, pointer, indices, "pointer", llvm::cast<llvm::Instruction>(in));

                            in->setOperand(i,getelement);
                        }
                    }
                } else if(llvm::isa<llvm::CallInst>(in)) {
                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst>(in);
                    for (size_t i = 0; i < in_c->getNumOperands()-1; i++) {

                        llvm::GEPOperator* gepop = llvm::dyn_cast<llvm::GEPOperator>(in_c->getArgOperand(i));

                        bool is_gepop;
                        is_gepop = llvm::dyn_cast<llvm::GEPOperator>(in->getOperand(i)) != NULL;
                        is_gepop = is_gepop && llvm::dyn_cast<llvm::GetElementPtrInst>(in->getOperand(i)) == NULL;

                        if(is_gepop) {
                            llvm::Value* pointer = gepop->getPointerOperand();
                            llvm::User::op_iterator idxbegin = gepop->idx_begin();
                            llvm::User::op_iterator idxend   = gepop->idx_end();
                            std::vector<llvm::Value*> indices(idxbegin, idxend);

                            llvm::GetElementPtrInst* getelement = llvm::GetElementPtrInst::Create(NULL, pointer, indices, "pointer", llvm::cast<llvm::Instruction>(in));

                            in->setOperand(i,getelement);
                        }
                    }
                } else if(llvm::isa<llvm::GetElementPtrInst>(in)) {

                    llvm::GetElementPtrInst* in_g = llvm::cast<llvm::GetElementPtrInst>(in);

                    llvm::GEPOperator* gepop = llvm::dyn_cast<llvm::GEPOperator>(in_g->getPointerOperand());

                    bool is_gepop;
                    is_gepop = llvm::dyn_cast<llvm::GEPOperator>(in_g->getPointerOperand()) != NULL;
                    is_gepop = is_gepop && llvm::dyn_cast<llvm::GetElementPtrInst>(in_g->getPointerOperand()) == NULL;

                    if(is_gepop) {
                        llvm::Value* pointer = gepop->getPointerOperand();
                        llvm::User::op_iterator idxbegin = gepop->idx_begin();
                        llvm::User::op_iterator idxend   = gepop->idx_end();
                        std::vector<llvm::Value*> indices(idxbegin, idxend);

                        llvm::GetElementPtrInst* getelement = llvm::GetElementPtrInst::Create(NULL, pointer, indices, "pointer", llvm::cast<llvm::Instruction>(in));

                        in->setOperand(0,getelement);
                    }
                }
            }
        }
    }
    return false;
}
