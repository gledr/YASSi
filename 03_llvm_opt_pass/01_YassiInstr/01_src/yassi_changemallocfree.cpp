/**
 * @file yassi_changemallocfree.hpp
 * @brief Optimization Pass to forward malloc/free calls to Yassi
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
#include "yassi_changemallocfree.hpp"

using namespace Yassi::OptPass::Execute;


char ChangeMallocFreePass::ID = 0;
static llvm::RegisterPass<ChangeMallocFreePass> ChangeMallocFree("instr_malloc", "Malloc Free");

/**
 * @brief Constructor
 */
ChangeMallocFreePass::ChangeMallocFreePass():
    InstrBase(),
    llvm::ModulePass(ChangeMallocFreePass::ID)
{
}

/**
 * @brief Destructor
 */
ChangeMallocFreePass::~ChangeMallocFreePass()
{
}

/**
 * @brief Overridden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool ChangeMallocFreePass::runOnModule(llvm::Module& M)
{
    std::vector<llvm::Instruction*> instr_to_rm;

    for ( auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun ) {
        for ( auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb ) {
            for ( auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in ) {
                if (llvm::isa<llvm::CallInst>(in)) {

                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst> (in);
                    
                    bool hasname = in_c->getCalledFunction();
                    std::string fn_name;
                    if (hasname) {

                        fn_name = in_c->getCalledFunction()->getName().str();

                        if (fn_name.find(BACKEND_FN_MALLOC) == 0) {
                            std::string argument = this->operandname(in_c->getArgOperand(0));
                            llvm::GlobalVariable* c1 = this->make_global_str(M, argument);

                            llvm::FunctionType* malloc_type =
                                llvm::TypeBuilder<void*(char*), false>::get(M.getContext());
                            llvm::Function* malloc_fun =
                                llvm::cast<llvm::Function>(M.getOrInsertFunction(BACKEND_FN_YASSI_MALLOC, malloc_type));
                            in_c->setCalledFunction(malloc_type, malloc_fun);
                            in_c->setArgOperand(0, this->pointerToArray(M, c1));

                        } else if (fn_name.find(BACKEND_FN_FREE) == 0){
                            instr_to_rm.push_back (llvm::cast<llvm::Instruction>(in));
                            
                            in->dump();

                            llvm::FunctionType* free_type =
                                llvm::TypeBuilder<void(char*), false>::get(M.getContext());
                            llvm::Function* free_fun =
                                llvm::cast<llvm::Function>(M.getOrInsertFunction(BACKEND_FN_YASSI_FREE, free_type));

                            llvm::BasicBlock::iterator insertpos = in;
                            insertpos++;
                            std::cerr << "asdf" << std::endl;
                            in_c->getArgOperand(0)->dump();
                            std::string nameass = this->operandname (in_c->getArgOperand (0));
                            std::cerr << nameass << std::endl;
                            llvm::GlobalVariable* c1 = this->make_global_str(M, nameass);

                            std::vector<llvm::Value*> params;
                            params.push_back(this->pointerToArray(M,c1));

                            c1->dump();
                            
                            llvm::CallInst::Create(free_fun,
                                                   params,
                                                   "",
                                                   llvm::cast<llvm::Instruction>(insertpos));
                        }
                    }
                }
            }
        }
    }
    
    for (auto it: instr_to_rm) {
        it->eraseFromParent();
    }

    return false;
}
