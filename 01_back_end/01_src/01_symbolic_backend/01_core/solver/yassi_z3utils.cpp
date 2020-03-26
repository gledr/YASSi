/** 
 * @file yassi_z3utils.cpp
 * @brief Utility Classes for Z3
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
 * @author Sebastian Pointner
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
#include "yassi_z3utils.hpp"

using namespace Yassi::Backend::Execute;

/**
 * @brief Calculate the Sum of a Vector
 * 
 * @param expr The Vector Holing the Items
 * @return z3::expr
 */
z3::expr Z3Utils::mk_add_bv(z3::expr_vector const & expr)
{
    z3::expr adder = expr[0];
    
    if(expr.size() >= 1){
        for(size_t i = 0; i < expr.size()-1; ++i){
            adder = adder + expr[i+1];
        }
    }
   return adder;
}

/**
 * @brief Wrapper for Z3 C Function for Solver Verions
 * 
 * @return std::string
 */
std::string Z3Utils::get_solver_version()
{
    return Z3_get_full_version();
}
