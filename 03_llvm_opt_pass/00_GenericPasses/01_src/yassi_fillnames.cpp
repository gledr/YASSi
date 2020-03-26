/** 
 * @file yassi_fillnames.hpp
 * @brief Optimization Pass to Prepare used Name Declaration for Symbolic Executiom
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
#include "yassi_fillnames.hpp"

using namespace Yassi::OptPass;
using namespace Yassi::Utils;


char FillNamesPass::ID = 0;
static llvm::RegisterPass<FillNamesPass> FillNames("instr_fill_names", "Fill Names");

FillNamesPass::FillNamesPass(): 
    BasePass(), llvm::ModulePass(FillNamesPass::ID) 
{

}

FillNamesPass::~FillNamesPass() 
{

}

bool FillNamesPass::runOnModule(llvm::Module& M) 
{
    this->change_dot_names(M);
    this->put_operator_names(M);
    this->put_block_names(M);
    this->put_global_names(M);

    return false;
}

void FillNamesPass::change_dot_names(llvm::Module &M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(in->hasName()) {
                    std::string name = in->getName();
                    BaseUtils::replace(name, ".", "");
                    in->setName(name);
                }
            }
        }
    }
}

void FillNamesPass::put_operator_names(llvm::Module &M ) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        llvm::Function::arg_iterator arg_begin = fun->arg_begin();
        llvm::Function::arg_iterator arg_end   = fun->arg_end();
        for(auto it = arg_begin; it != arg_end; it++ ) {
            if(!it->hasName()) it->setName("a");
        }
        
        std::string internal_reg = "__reg";

        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {

                if(llvm::isa<llvm::UnaryInstruction>(in)) {
                    if(!in->getOperand(0)->hasName())        in->getOperand(0)->setName(internal_reg);
                    if(!in->hasName())                       in->setName(internal_reg);
                }
                if(llvm::isa<llvm::BinaryOperator>(in)) {
                    if(!in->getOperand(0)->hasName())        in->getOperand(0)->setName(internal_reg);
                    if(!in->getOperand(1)->hasName())        in->getOperand(1)->setName(internal_reg);
                    if(!in->hasName())                       in->setName(internal_reg);
                }
                if(llvm::isa<llvm::CmpInst>(in)) {
                    if(!in->getOperand(0)->hasName())        in->getOperand(0)->setName(internal_reg);
                    if(!in->getOperand(1)->hasName())        in->getOperand(1)->setName(internal_reg);
                    if(!in->hasName())                       in->setName(internal_reg);
                }
                if(llvm::isa<llvm::GetElementPtrInst>(in)) {
                    if(!in->hasName())                       in->setName(internal_reg);
                }
                if(llvm::isa<llvm::CallInst>(in)) {
                    if(!(in->getType()->isVoidTy())){
                        llvm::CallInst * tmp = llvm::dyn_cast<llvm::CallInst>(in);
            
                        if(tmp->getCalledFunction() == nullptr){
                            tmp->setName("return_of_function_pointer");
                        } else {
                            tmp->setName("return_of_" + this->demangle_fn_name(tmp->getCalledFunction()->getName().str()));
                        }
                    }
                }
            }
        }
    }
}

void FillNamesPass::put_block_names(llvm::Module &M ) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            if(!bb->hasName()) bb->setName("b");
        }
    }
}

void FillNamesPass::put_global_names(llvm::Module &M) 
{
    for(auto gl = M.global_begin(), gl_end = M.global_end();  gl != gl_end; ++gl) {
        llvm::GlobalVariable* global_var = llvm::cast<llvm::GlobalVariable>(gl);
        if( !global_var->hasName()) global_var->setName("g");
    }
}
