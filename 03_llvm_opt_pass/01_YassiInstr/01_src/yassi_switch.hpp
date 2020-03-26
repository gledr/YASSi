/**
 * @file yassi_switch.hpp
 * @brief Optimization Pass to Extract Switch Targets from LLVM's Switch Function
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
#ifndef YASSI_SWITCH_PASS_HPP
#define YASSI_SWITCH_PASS_HPP

#include "yassi_instrbase.hpp"

namespace Yassi::OptPass::Execute {

/**
 * @class SwitchPass
 * @brief Extract Switch Targets from LLVM's Switch Function
 */
class SwitchPass: public llvm::ModulePass, virtual public InstrBase {
public:
    SwitchPass();

    ~SwitchPass();

    bool runOnModule(llvm::Module& M) override;

private:
    static char ID;
};

}

#endif /* YASSI_SWITCH_PASS_HPP */
