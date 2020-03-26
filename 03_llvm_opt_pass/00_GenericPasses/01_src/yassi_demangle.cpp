/** 
 * @file yassi_demangle.cpp
 * @brief Optimization Pass to Demangle C++ declarations
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
#include "yassi_demangle.hpp"

using namespace Yassi::OptPass;
using namespace Yassi::Utils;


char DemanglePass::ID = 0;
static llvm::RegisterPass<DemanglePass> DemangleNames("instr_demangle_functions", "Demangle Names");

DemanglePass::DemanglePass(): 
    BasePass(), llvm::ModulePass(DemanglePass::ID) 
{

}

DemanglePass::~DemanglePass() 
{

}

bool DemanglePass::runOnModule(llvm::Module& M) 
{
    for(auto gl = M.global_begin(), gl_end = M.global_end();  gl != gl_end; ++gl) {
        std::string demangled = boost::core::demangle(gl->getName().str().c_str());
        std::vector<std::string> token = BaseUtils::tokenize(demangled, "::");
        if(token.size() > 1) {
            gl->setName(token[0] + "_" + token[1]);
        }
    }
    return false;
}
