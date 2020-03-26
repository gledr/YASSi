/** 
 * @file yassi_instrbase.cpp
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
#include "yassi_instrbase.hpp"

using namespace Yassi::OptPass::Execute;

std::string const InstrBase::YASSI_BACKEND_FN_BEGIN_BB           = "__YASSI_begin_bb";
std::string const InstrBase::YASSI_BACKEND_FN_END_BB             = "__YASSI_end_bb";
    
std::string const InstrBase::YASSI_BACKEND_FN_LOAD               = "__YASSI_load_instr";
std::string const InstrBase::YASSI_BACKEND_FN_STORE              = "__YASSI_store_instr";

std::string const InstrBase::YASSI_BACKEND_FN_BEGIN_FN           = "__YASSI_begin_fn";
std::string const InstrBase::YASSI_BACKEND_FN_END_FN             = "__YASSI_end_fn";

std::string const InstrBase::YASSI_BACKEND_FN_BEGIN_SIM          = "__YASSI_begin_sim";
std::string const InstrBase::YASSI_BACKEND_FN_END_SIM            = "__YASSI_end_sim";

std::string const InstrBase::YASSI_BACKEND_FN_BRANCH_COND        = "__YASSI_br_instr_cond";
std::string const InstrBase::YASSI_BACKEND_FN_BRANCH_INCOND      = "__YASSI_br_instr_incond";

std::string const InstrBase::YASSI_BACKEND_FN_BINARY_OP          = "__YASSI_binary_op";
std::string const InstrBase::YASSI_BACKEND_FN_COMPARE            = "__YASSI_cmp_instr";
std::string const InstrBase::YASSI_BACKEND_FN_SELECT             = "__YASSI_select_op";

std::string const InstrBase::YASSI_BACKEND_FN_ALLOCA             = "__YASSI_alloca_instr";
std::string const InstrBase::YASSI_BACKEND_FN_GETELEMENTPTR      = "getelementptr";
std::string const InstrBase::YASSI_BACKEND_FN_CAST               = "__YASSI_cast_instruction";

std::string const InstrBase::YASSI_BACKEND_FN_CALL_INSTR         = "__YASSI_call_instruction";
std::string const InstrBase::YASSI_BACKEND_FN_CALL_POST          = "__YASSI_call_instruction_post";
std::string const InstrBase::YASSI_BACKEND_FN_FN_RETURN          = "__YASSI_return_instruction";

std::string const InstrBase::YASSI_BACKEND_FN_MEMCPY             = "__YASSI_memcpy";
std::string const InstrBase::YASSI_BACKEND_FN_MEMSET             = "__YASSI_memset";

bool InstrBase::is_backend_symbolic_function(std::string const & _fn_name) 
{
    std::string fn_name = this->demangle_fn_name(_fn_name);

    if(fn_name == BACKEND_FN_GLOBAL_INIT            ) return true;
    if(fn_name == YASSI_BACKEND_FN_BEGIN_SIM       ) return true;
    if(fn_name == YASSI_BACKEND_FN_END_SIM         ) return true;
    if(fn_name == YASSI_BACKEND_FN_FN_RETURN       ) return true;
    if(fn_name == YASSI_BACKEND_FN_CALL_POST       ) return true;
    if(fn_name == YASSI_BACKEND_FN_CALL_INSTR      ) return true;
    if(fn_name == YASSI_BACKEND_FN_BRANCH_COND     ) return true;
    if(fn_name == YASSI_BACKEND_FN_BRANCH_INCOND   ) return true;
    if(fn_name == YASSI_BACKEND_FN_BEGIN_FN        ) return true;
    if(fn_name == YASSI_BACKEND_FN_END_FN          ) return true;
    if(fn_name == YASSI_BACKEND_FN_BEGIN_BB        ) return true;
    if(fn_name == YASSI_BACKEND_FN_END_BB          ) return true;
    if(fn_name == YASSI_BACKEND_FN_ALLOCA          ) return true;
    if(fn_name == YASSI_BACKEND_FN_STORE           ) return true;
    if(fn_name == YASSI_BACKEND_FN_LOAD            ) return true;
    if(fn_name == YASSI_BACKEND_FN_BINARY_OP       ) return true;
    if(fn_name == YASSI_BACKEND_FN_CAST            ) return true;
    if(fn_name == YASSI_BACKEND_FN_COMPARE         ) return true;
    if(fn_name == YASSI_BACKEND_FN_GETELEMENTPTR   ) return true;
    if(fn_name == YASSI_BACKEND_FN_MEMCPY          ) return true;
    if(fn_name == YASSI_BACKEND_FN_MEMSET          ) return true;
    if(fn_name == BACKEND_FN_YASSI_MALLOC          ) return true;
    if(fn_name == BACKEND_FN_YASSI_FREE            ) return true;
    if(fn_name == BACKEND_FN_FP                     ) return true;
    if(fn_name == BACKEND_FN_ASSUME                 ) return true;
    if(fn_name == BACKEND_FN_ASSERTION              ) return true;
    if(fn_name == BACKEND_FN_VERIFIER_ASSUME        ) return true;
    if(fn_name == BACKEND_FN_VERIFIER_ASSERT        ) return true;
    if(fn_name == BACKEND_FN_FORCEFREE_LOCAL        ) return true;
    if(fn_name == BACKEND_FN_FORCEFREE_GLOBAL       ) return true;
    if(fn_name == BACKEND_FN_DEBUG_MSG              ) return true;

    return false;
}
