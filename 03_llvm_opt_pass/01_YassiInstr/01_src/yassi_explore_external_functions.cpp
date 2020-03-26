/** 
 * @file yassi_explore_external_functions.cpp
 * @brief Optimization Pass to explore external function calls
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
#include "yassi_explore_external_functions.hpp"

using namespace Yassi::OptPass::Execute;

char ExploreExternalFunctionsPass::ID = 0;

ExploreExternalFunctionsPass::ExploreExternalFunctionsPass(): 
    InstrBase(),
    llvm::ModulePass(ExploreExternalFunctionsPass::ID)
{
}

ExploreExternalFunctionsPass::~ExploreExternalFunctionsPass() 
{
}

bool ExploreExternalFunctionsPass::runOnModule(llvm::Module& M) 
{
    for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
        if(fun->begin() == fun->end()){
            p_db->insert_external_function(this->demangle_fn_name(fun->getName().str()));
        } else {
            p_db->insert_internal_function(this->demangle_fn_name(fun->getName().str()));
        }
    }
    return false;
}
