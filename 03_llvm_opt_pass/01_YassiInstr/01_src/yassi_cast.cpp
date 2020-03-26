/** 
 * @file yassi_cast.cpp
 * @brief Handle LLVM's Cast Operations for Symbolic Execution
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
#include "yassi_cast.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Types;


char CastPass::ID = 0;

/**
 * @brief Constructor
 */
CastPass::CastPass():
    InstrBase(),
    llvm::ModulePass(ID)
{
}

/**
 * @brief Destructor
 */
CastPass::~CastPass()
{
}

/**
 * @brief Overriden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool CastPass::runOnModule(llvm::Module& M)
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        for(auto bb = fun->begin(), block_end = fun->end(); bb != block_end; ++bb) {
            for(auto in = bb->begin(), instruction_end = bb->end(); in != instruction_end; ++in) {
                if(llvm::isa<llvm::CastInst>(in)) {
                    if(in->getName().str() == "reg2mem alloca point" ){
                        continue;
                    }

                    llvm::CastInst* cast_in = llvm::dyn_cast<llvm::CastInst>(in);
                    std::string nameres = this->make_register_name(in->getName().str());
                    std::string nameop1 = this->operandname( in->getOperand(0) );
                    std::string sext = llvm::dyn_cast<llvm::SExtInst>(in) ? "true" : "false";

                    // Find Type To
                    llvm::Type* to_type = cast_in->getDestTy();
                    std::vector<BaseType*> types;
                    
                    types.push_back(p_type_factory->get_type_by_enum(static_cast<TypeID>(to_type->getTypeID()), to_type->getPrimitiveSizeInBits()));
                    
                    if(cast_in->getDestTy()->isPointerTy()){
                        llvm::PointerType* ptr = llvm::dyn_cast<llvm::PointerType>(cast_in->getDestTy());
                        llvm::Type* dst_type = ptr->getPointerElementType();
                        types.push_back(p_type_factory->get_type_by_enum(static_cast<TypeID>(dst_type->getTypeID()), dst_type->getPrimitiveSizeInBits()));
                    }
                     
                    std::stringstream types_str;
                    for(auto itor: types){
                        types_str << itor->get_type_identifier() << ":";
                    }
                    
                    llvm::GlobalVariable* c1 = this->make_global_str(M, nameres);
                    llvm::GlobalVariable* c2 = this->make_global_str(M, nameop1);
                    llvm::GlobalVariable* c3 = this->make_global_str(M, types_str.str());
                    llvm::GlobalVariable* c4 = this->make_global_str(M, sext);

                    llvm::FunctionType* cast_op_type = llvm::TypeBuilder<void(char*, char*, char*, char*), false>::get(M.getContext());
                    llvm::Function* cast_op_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(YASSI_BACKEND_FN_CAST, cast_op_type));

                    llvm::BasicBlock::iterator insertpos = in;
                    insertpos++;

                    std::vector<llvm::Value*> params;
                    params.push_back(this->pointerToArray(M,c1));
                    params.push_back(this->pointerToArray(M,c2));
                    params.push_back(this->pointerToArray(M,c3));
                    params.push_back(this->pointerToArray(M,c4));
                    llvm::CallInst::Create(cast_op_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
                }
            }
        }
    }
    return false;
}
