/** 
 * @file yassi_functionpointer.cpp
 * @brief Optimization Pass to handle function pointer
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
#include "yassi_functionpointer.hpp"

using namespace Yassi::OptPass::Execute;

char FunctionPointerPass::ID = 0;

FunctionPointerPass::FunctionPointerPass():
    InstrBase(),
    llvm::ModulePass(FunctionPointerPass::ID)
{
}

FunctionPointerPass::~FunctionPointerPass()
{
}

bool FunctionPointerPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::CallInst>(in)) {
                    
                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst>(in);
                    bool hasname = in_c->getCalledFunction();

                    if(!hasname) {
                        llvm::Value* called_v = in_c->getCalledValue();
                        if(!llvm::isa<llvm::ConstantExpr>(called_v) ) {
                            llvm::BasicBlock::iterator insertpos = in;

                            std::string register_name = this->operandname(called_v);
        
                            llvm::GlobalVariable* c1 = this->make_global_str(M, register_name);
                    
                            llvm::FunctionType* func_type = llvm::FunctionType::get(called_v->getType(), llvm::Type::getInt8PtrTy(M.getContext()), false);
                            llvm::Function* func_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(BACKEND_FN_FP, func_type));
                            
                            std::vector<llvm::Value*> params;
                            params.push_back(this->pointerToArray(M,c1));

                            llvm::CallInst* call = llvm::CallInst::Create(func_fun, params, "hola", llvm::cast<llvm::Instruction>(insertpos));
                            in->setOperand(in->getNumOperands()-1,call);
                        }
                    }
                }
            }
        }
    }
    return false;
}
