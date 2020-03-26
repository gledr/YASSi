/** 
 * @file yassi_loadstore.cpp
 * @brief Optimization Pass to Handle LLVMs Load and Store Architecture
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
#include "yassi_loadstore.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Types;

char LoadStorePass::ID = 0;

LoadStorePass::LoadStorePass():
    InstrBase(),
    llvm::ModulePass(LoadStorePass::ID)
{
}

LoadStorePass::~LoadStorePass()
{
}

bool LoadStorePass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::LoadInst>(in)) {
                    
                    llvm::LoadInst * in_load = llvm::cast<llvm::LoadInst>(in);
                    std::string nameres = this->make_register_name(in->getName().str());
                    BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(in_load->getType()->getTypeID()), in_load->getType()->getPrimitiveSizeInBits());
                    std::string nameop1 = this->operandname(in->getOperand(0));
        
                    llvm::GlobalVariable* c1 = this->make_global_str(M, nameres);
                    llvm::GlobalVariable* c2 = this->make_global_str(M, type->get_type_identifier());
                    llvm::GlobalVariable* c3 = this->make_global_str(M, nameop1);
                    llvm::GlobalVariable* c4 = this->make_global_str(M, this->line_number_of_instruction(*in));

                    llvm::FunctionType* load_op_type = llvm::TypeBuilder<void(char*, char*, char*, char*), false>::get(M.getContext());
                    assert (load_op_type != nullptr);
                    llvm::Value* load_op_fun = llvm::cast<llvm::Value>(M.getOrInsertFunction(YASSI_BACKEND_FN_LOAD, load_op_type));
    
                    llvm::BasicBlock::iterator insertpos = in;
                    insertpos++;

                    std::vector<llvm::Value*> params;
                    params.push_back(this->pointerToArray(M, c1));
                    params.push_back(this->pointerToArray(M, c2));
                    params.push_back(this->pointerToArray(M, c3));
                    params.push_back(this->pointerToArray(M, c4));

                    llvm::CallInst::Create(load_op_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));

                } else if(llvm::isa<llvm::StoreInst>(in)) {
                    
                    std::string nameop1 = this->operandname(in->getOperand(0));
                    std::string nameop2 = this->operandname(in->getOperand(1));

                    llvm::GlobalVariable* c1 = this->make_global_str(M, nameop1);
                    llvm::GlobalVariable* c2 = this->make_global_str(M, nameop2);
                    llvm::GlobalVariable* c3 = this->make_global_str(M, this->line_number_of_instruction(*in));

                    llvm::FunctionType * store_op_type = llvm::TypeBuilder<void(char*, char*, char*), false>::get(M.getContext());
                    llvm::Function* store_op_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_STORE, store_op_type));
    
                    llvm::BasicBlock::iterator insertpos = in;
                    insertpos++;

                    std::vector<llvm::Value*> params;
                    params.push_back(this->pointerToArray(M, c1));
                    params.push_back(this->pointerToArray(M, c2));
                    params.push_back(this->pointerToArray(M, c3));

                    llvm::CallInst::Create(store_op_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
                }
            }
        }
    }
    return false;
}
