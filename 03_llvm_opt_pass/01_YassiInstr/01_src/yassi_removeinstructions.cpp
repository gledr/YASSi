/** 
 * @file yassi_removeinstructions.cpp
 * @brief Optimization Pass to Remove Obsolete Instructions
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
#include "yassi_removeinstructions.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Types;

char RemoveInstructionsPass::ID = 0;

RemoveInstructionsPass::RemoveInstructionsPass(): 
    InstrBase(), 
    llvm::ModulePass(RemoveInstructionsPass::ID) 
{
}

RemoveInstructionsPass::~RemoveInstructionsPass() 
{
}

bool RemoveInstructionsPass::runOnModule(llvm::Module& M) 
{
    this->ret_zero(M);
    this->callinstr_operands(M);
    this->rm_instr(M);

    return false;
}

llvm::Constant* RemoveInstructionsPass::get_zero_of_type(llvm::Type* _type, llvm::Module& M) 
{
    llvm::Constant* ret;

    BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(_type->getTypeID()), _type->getPrimitiveSizeInBits());
    if     (type->is_int32())   ret = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, llvm::StringRef("0"), 10));
    else if(type->is_int16())   ret = llvm::ConstantInt::get(M.getContext(), llvm::APInt(16, llvm::StringRef("0"), 10));
    else if(type->is_int64())   ret = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef("0"), 10));
    else if(type->is_int8())    ret = llvm::ConstantInt::get(M.getContext(), llvm::APInt( 8, llvm::StringRef("0"), 10));
    else if(type->is_int1())    ret = llvm::ConstantInt::get(M.getContext(), llvm::APInt( 1, llvm::StringRef("0"), 10));
    else if(type->is_pointer()) ret = llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(_type));
    else if(type->is_double())  ret = llvm::ConstantFP::get(_type, 0);

    else {
        std::cerr << "type:" << std::endl;
        _type->dump();
        std::cerr << type->get_type_identifier() << std::endl;
        assert(0 && "Unknown Type");
    }

    return ret;
}

void RemoveInstructionsPass::callinstr_operands(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::CallInst>(in)) {
                    
                    llvm::CallInst* in_c = llvm::cast<llvm::CallInst>(in);
                    assert (in_c != nullptr);
                    if(in_c->getCalledFunction() == nullptr){
                        continue;
                    }
                    
                    std::string fn_name = in_c->getCalledFunction()->getName().str();

                    if((in_c->getCalledFunction() && this->is_backend_symbolic_function(fn_name)) || 
                       (in_c->getCalledFunction() && this->is_special_llvm_function(fn_name))){
                        continue;
                    }

                    for (size_t i = 0; i < in->getNumOperands()-1; i++) {
                        llvm::Constant* zero = get_zero_of_type(in->getOperand(i)->getType(), M);
                            in->setOperand(i,zero);
                    }
                }
            }
        }
    }
}

void RemoveInstructionsPass::ret_zero(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::ReturnInst>(in)) {
                    llvm::ReturnInst * ret_instr = llvm::dyn_cast<llvm::ReturnInst>(in);
                    if (ret_instr->getType()->getTypeID() != llvm::Type::VoidTyID && ret_instr->getNumOperands() > 0){
                        llvm::Constant* zero = get_zero_of_type(in->getOperand(0)->getType(), M);
                        in->setOperand(0,zero);
                    }
                }
            }
        }
    }
}

void RemoveInstructionsPass::rm_instr(llvm::Module& M) 
{
    std::vector<llvm::Instruction*> rm_instr;
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                llvm::Instruction* to_remove = llvm::cast<llvm::Instruction>(in);

                if(llvm::isa<llvm::BinaryOperator>(in)          ) rm_instr.push_back(to_remove);
                if(llvm::isa<llvm::CmpInst>(in)                 ) rm_instr.push_back(to_remove);
                if(llvm::isa<llvm::LoadInst>(in)                ) rm_instr.push_back(to_remove);
                if(llvm::isa<llvm::StoreInst>(in)               ) rm_instr.push_back(to_remove);
                if(llvm::isa<llvm::AllocaInst>(in)              ) rm_instr.push_back(to_remove);
                if(llvm::isa<llvm::CastInst>(in)                ) rm_instr.push_back(to_remove);
                if(llvm::isa<llvm::GetElementPtrInst>(in)       ) rm_instr.push_back(to_remove);
            }
        }
    }

    for(auto it = rm_instr.end()-1; it != rm_instr.begin(); it-- ) {
        (*it)->dump();
        if((*it)->getNumUses() == 0)
            (*it)->eraseFromParent();
    }

   // (*rm_instr.begin())->eraseFromParent();
}
