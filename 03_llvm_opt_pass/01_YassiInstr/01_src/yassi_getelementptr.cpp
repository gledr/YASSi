/** 
 * @file yassi_getelementptr.cpp
 * @brief Optimization Pass to handle LLVM's GetElementPtrInst
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
#include "yassi_getelementptr.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Types;

char GetElementPtrPass::ID = 0;

GetElementPtrPass::GetElementPtrPass():
    InstrBase(),
    llvm::ModulePass(GetElementPtrPass::ID)
{
}

GetElementPtrPass::~GetElementPtrPass()
{
}

bool GetElementPtrPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::GetElementPtrInst>(in)) {

                    llvm::GetElementPtrInst* in_g = llvm::cast<llvm::GetElementPtrInst>(in);
                
                    llvm::Value* pointer = in_g->getPointerOperand();
                    llvm::GlobalVariable* pointer_global = llvm::dyn_cast<llvm::GlobalVariable>(pointer);

                    std::string nameres = this->make_register_name(in->getName().str());

                    std::string nameop1;
                    if(pointer_global) {
                        nameop1 = this->make_global_name(pointer->getName().str());
                    } else {
                        nameop1 = this->make_register_name(pointer->getName().str());
                    }

                    std::vector<std::string> indexes = get_indexes(in_g);

                    std::string indexes_str;
                    for(auto it : indexes) {
                        indexes_str += it + VARIABLE_SEPERATOR;
                    }

                    std::string offset_tree = this->get_offset_tree(in_g->getPointerOperandType());

                    llvm::GlobalVariable* c1 = this->make_global_str(M, nameres);
                    llvm::GlobalVariable* c2 = this->make_global_str(M, nameop1);
                    llvm::GlobalVariable* c3 = this->make_global_str(M, indexes_str);
                    llvm::GlobalVariable* c4 = this->make_global_str(M, offset_tree);
                    llvm::GlobalVariable* c5 = this->make_global_str(M, this->line_number_of_instruction(*in));

                    llvm::FunctionType * gep_type = llvm::TypeBuilder<void(char*, char*, char*, char*, char*), false>::get(M.getContext());
                    llvm::Function* gep_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_GETELEMENTPTR, gep_type));

                    llvm::BasicBlock::iterator insertpos = in;
                    insertpos++;

                    std::vector<llvm::Value*> params;
                    params.push_back(this->pointerToArray(M,c1));
                    params.push_back(this->pointerToArray(M,c2));
                    params.push_back(this->pointerToArray(M,c3));
                    params.push_back(this->pointerToArray(M,c4));
                    params.push_back(this->pointerToArray(M,c5));
                    llvm::CallInst::Create(gep_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
                }
            }
        }
    }
    return false;
}

std::vector<std::string> GetElementPtrPass::get_indexes(llvm::GetElementPtrInst* instr) 
{
    std::vector<std::string> ret;

    for(auto it = instr->idx_begin(), it_end = instr->idx_end(); it != it_end; it++) {
        llvm::ConstantInt* CI = llvm::dyn_cast<llvm::ConstantInt>(it->get());
        if(CI) {
            int64_t val = CI->getSExtValue();
            ret.push_back(this->make_constant(POINTERTYPE, std::to_string(val)));
        } else {
            llvm::Value* value = it->get();
            ret.push_back(this->make_register_name(value->getName().str()));
        }
    }
    return ret;
}
