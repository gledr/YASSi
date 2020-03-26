/** 
 * @file yassi_instrbase.hpp
 * @brief Base Class for all Instrumentation Passes
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
#ifndef YASSI_INSTRBASE_HPP
#define YASSI_INSTRBASE_HPP

#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/ValueMapper.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

#ifdef YASSI_INSTR_PASS
    #include "yassi_basepass.hpp"
    #include "yassi_datastructuretree.hpp"
#else 
    #include "../../00_GenericPasses/01_src/yassi_basepass.hpp"
    #include "../../../04_utils/03_datastructures/yassi_datastructuretree.hpp"
#endif

namespace Yassi::OptPass::Execute {

/**
 * @class InstrBase
 * @brief Base Class for all Instrumentation Passes
 */
class InstrBase: public virtual BasePass {
protected:
    bool is_backend_symbolic_function(std::string const & fn_name);
    
    static std::string const YASSI_BACKEND_FN_BEGIN_BB;
    static std::string const YASSI_BACKEND_FN_END_BB;
    
    static std::string const YASSI_BACKEND_FN_LOAD;
    static std::string const YASSI_BACKEND_FN_STORE;
    
    static std::string const YASSI_BACKEND_FN_BEGIN_FN;
    static std::string const YASSI_BACKEND_FN_END_FN;
    
    static std::string const YASSI_BACKEND_FN_BEGIN_SIM;
    static std::string const YASSI_BACKEND_FN_END_SIM;
    
    static std::string const YASSI_BACKEND_FN_BRANCH_COND;
    static std::string const YASSI_BACKEND_FN_BRANCH_INCOND;
    
    static std::string const YASSI_BACKEND_FN_BINARY_OP;
    static std::string const YASSI_BACKEND_FN_COMPARE;
    static std::string const YASSI_BACKEND_FN_SELECT;

    static std::string const YASSI_BACKEND_FN_ALLOCA;
    static std::string const YASSI_BACKEND_FN_GETELEMENTPTR;
    static std::string const YASSI_BACKEND_FN_CAST;
    
    static std::string const YASSI_BACKEND_FN_CALL_INSTR;
    static std::string const YASSI_BACKEND_FN_CALL_POST;
    static std::string const YASSI_BACKEND_FN_FN_RETURN;
    
    static std::string const YASSI_BACKEND_FN_MEMCPY;
    static std::string const YASSI_BACKEND_FN_MEMSET;
};

}

#endif /* YASSI_INSTRBASE_HPP */
