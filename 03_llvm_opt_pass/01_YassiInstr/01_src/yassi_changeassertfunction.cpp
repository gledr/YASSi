/**
 * @file yassi_changeassertfunction.cpp
 * @brief Optimization Pass Modify Assertions for Yassi
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
#include "yassi_changeassertfunction.hpp"

using namespace Yassi::OptPass::Execute;


char ChangeAssertFunctionPass::ID = 0;

ChangeAssertFunctionPass::ChangeAssertFunctionPass():
    InstrBase(),
    llvm::ModulePass(ChangeAssertFunctionPass::ID)
{
}

ChangeAssertFunctionPass::~ChangeAssertFunctionPass()
{
}

bool ChangeAssertFunctionPass::runOnModule(llvm::Module& M)
{
    std::vector<llvm::Instruction*> instr_to_rm;

    for ( auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun ) {
        for ( auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb ) {
            for ( auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in ) {
                if (llvm::isa<llvm::CallInst>(in)) {

                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst> (in);
 
                    bool hasname = in_c->getCalledFunction();
                    std::string fn_name;
                    if ( hasname ) {
                        fn_name = in_c->getCalledFunction()->getName().str();
                        if (fn_name.find(BACKEND_FN_VERIFIER_ASSERT) != std::string::npos) {
                            std::cout << fn_name << std::endl;
                            instr_to_rm.push_back (llvm::cast<llvm::Instruction>(in));

                            std::string nameass = this->operandname (in_c->getArgOperand (0));
                            std::string position = this->line_number_of_instruction(*in);

                            llvm::GlobalVariable* c1 = this->make_global_str(M, nameass);
                            llvm::GlobalVariable* c2 = this->make_global_str(M, position);

                            llvm::FunctionType* ch_assert_type = llvm::TypeBuilder<void(char*, char*), false>::get(M.getContext());
                            llvm::Function* ch_assert_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(BACKEND_FN_ASSERTION, ch_assert_type));
                            
                            llvm::BasicBlock::iterator insertpos = in;
                            insertpos++;

                            std::vector<llvm::Value*> params;
                            params.push_back(this->pointerToArray (M,c1));
                            params.push_back(this->pointerToArray (M,c2));
                            llvm::CallInst::Create(ch_assert_fun, params, "", llvm::cast<llvm::Instruction>(insertpos) );
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
