/**
 * @file yassi_changeprinft.cpp
 * @brief Optimization Pass to forward printf calls to Yassi
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
#include "yassi_changeprintf.hpp"

using namespace Yassi::OptPass::Execute;


char ChangePrintfPass::ID = 0;

/**
 * @brief Constructor
 */
ChangePrintfPass::ChangePrintfPass():
    InstrBase(),
    llvm::ModulePass(ChangePrintfPass::ID)
{
}

/**
 * @brief Destructor
 */
ChangePrintfPass::~ChangePrintfPass()
{
}

/**
 * @brief Overridden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool ChangePrintfPass::runOnModule(llvm::Module& M)
{
    std::vector<llvm::Instruction*> instr_to_rm;

    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::CallInst>(in)) {

                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst>(in);

                    bool hasname = in_c->getCalledFunction();
                    if(hasname) {
                        std::string fn_name = in_c->getCalledFunction()->getName().str();
                        if(fn_name.find("printf") != std::string::npos) {
                            instr_to_rm.push_back(llvm::cast<llvm::Instruction>(in));

                            std::string nameass = this->operandname(in_c->getArgOperand(0));
                            llvm::GlobalVariable* c1 = this->make_global_str(M, nameass);

                            llvm::FunctionType* fun_type = llvm::TypeBuilder<int(char*), false>::get(M.getContext());
                            llvm::Function* fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(BACKEND_FN_DEBUG_MSG, fun_type));

                            llvm::BasicBlock::iterator insertpos = in;
                            insertpos++;

                            std::vector<llvm::Value*> params;
                            params.push_back(this->pointerToArray(M,c1));

                            llvm::CallInst::Create(fun, params, "",llvm::cast<llvm::Instruction>(insertpos));
                        }
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
