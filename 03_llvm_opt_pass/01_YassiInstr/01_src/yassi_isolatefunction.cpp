/** 
 * @file yassi_isolatefunction.cpp
 * @brief Optimization Pass to Isolate Single Functions
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
#include "yassi_isolatefunction.hpp"

using namespace Yassi::OptPass::Execute;


char IsolateFunctionPass::ID = 0;
static llvm::RegisterPass<IsolateFunctionPass> IsolateFunction("instr_isolate_seed", "Isolate Seed Function");

/**
 * @brief Constructor
 */
IsolateFunctionPass::IsolateFunctionPass():
    llvm::ModulePass(IsolateFunctionPass::ID),
    InstrBase()
{
}

/**
 * @brief Destructor
 */
IsolateFunctionPass::~IsolateFunctionPass()
{
}

/**
 * @brief Overriden Optimization Function
 * 
 * @param M LLVM Module
 * @return bool
 */
bool IsolateFunctionPass::runOnModule(llvm::Module& M)
{
    std::string seed_function = p_settings["isolate_function"];
    std::string mangled_seed_function;

    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        if(this->demangle_fn_name(fun->getName()).compare(seed_function) == 0){
            mangled_seed_function = fun->getName();
            break;
        }
    }
    
    if(mangled_seed_function.empty()){
        std::cerr << "Can not find Seed Function" << std::endl;
        std::cerr << "No Isolation Possible" << std::endl;
        return false;
    }

    llvm::Function* fnseed = M.getFunction(mangled_seed_function);

    llvm::Function::arg_iterator arg_begin = fnseed->arg_begin();
    llvm::Function::arg_iterator arg_end   = fnseed->arg_end();

    std::vector<std::string> argNames;
    std::vector<llvm::Type*> argTypes;

    for(auto it = arg_begin; it != arg_end; it++ ){
        argNames.push_back(it->getName().str());
        llvm::Type* t = it->getType();
        argTypes.push_back(t);
    }

    M.getFunction("main")->eraseFromParent();

    llvm::FunctionType* main_type = llvm::TypeBuilder<void(void), false>::get(M.getContext());
    llvm::Function* main_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction("main", main_type));

    llvm::BasicBlock* entry = llvm::BasicBlock::Create(M.getContext(), "entry", main_fun, 0);

    std::vector<llvm::Value*> params;
    for (size_t i = 0; i < argNames.size(); i++) {
        std::string name = argNames[i];
        llvm::AllocaInst* ai = new llvm::AllocaInst(argTypes[i], 0, 0, name.c_str(), entry );
        llvm::LoadInst* ai_ptr = new llvm::LoadInst(ai,"",entry);
        params.push_back(ai_ptr);
    }

    llvm::CallInst::Create(fnseed, params, "", entry);
    llvm::ReturnInst::Create(M.getContext(), entry);

    return true;
}
