/** 
 * @file yassi_fillnames.cpp
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
#ifndef YASSI_FILLNAMES_PASS_HPP
#define YASSI_FILLNAMES_PASS_HPP

#include "yassi_basepass.hpp"

namespace Yassi::OptPass {

/**
 * @class FillNamesPass
 * @brief Optimization Pass to Prepare Name Conventions
 */
class FillNamesPass: public llvm::ModulePass, public virtual BasePass {
public:
    FillNamesPass();

    virtual ~FillNamesPass();

    bool runOnModule(llvm::Module& M) override;

    static char ID;

private:
    void change_dot_names(llvm::Module &M);
    
    void put_operator_names(llvm::Module &M );
    
    void put_block_names(llvm::Module &M );
    
    void put_global_names(llvm::Module &M);
};

}

#endif /* YASSI_FILLNAMES_PASS_HPP */
