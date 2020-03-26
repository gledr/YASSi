/** 
 * @file yassi_symbolicexecutor.hpp
 * @brief Symbolic Execution Core Class
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
#ifndef YASSI_SYMBOLICEXECUTOR_HPP
#define YASSI_SYMBOLICEXECUTOR_HPP

#include <string>
#include <memory>

#include <sys/wait.h>
#include <sys/prctl.h>

#include <yassi_object.hpp>
#include <yassi_database.hpp>
#include <yassi_types.hpp>
#include <yassi_variables.hpp>
#include <yassi_memory.hpp>
#include <yassi_memoryexporter.hpp>
#include <yassi_propagation.hpp>
#include <yassi_typecast.hpp>
#include <yassi_compare_operators.hpp>
#include <yassi_arithmetic_operators.hpp>
#include <yassi_pointerinstruction.hpp>
#include <yassi_loadstore.hpp>
#include "yassi_solver.hpp"
#include <yassi_forcefree.hpp>
#include <yassi_logger.hpp>
#include <yassi_baseutils.hpp>
#include <yassi_z3utils.hpp>

#include <yassi_llvm_enums.hpp>

namespace Yassi::Backend::Execute {

/**
 * @class SymbolicExecutor
 * @brief This call represent the main Symbolic Execution class.
 *
 * All LLVM calls end up here and will be split up into the subclasses.
 */
class SymbolicExecutor: public virtual Object{
public:
    SymbolicExecutor(Database* database, z3::context* z3_ctx, z3::solver* z3_slv);

    virtual ~SymbolicExecutor();

    void load_instruction(std::string const & dst,
                          std::string const & dst_type,
                          std::string const & addr);

    void store_instruction(std::string const & src,
                           std::string const & addr);

    void binary_instruction(std::string const & dst,
                            std::string const & op1,
                            std::string const & op2,
                            LLVMOpcode const & op);

    void compare_instruction(std::string const & dst,
                             std::string const & op1,
                             std::string const & op2,
                             int const & op);

    void alloca_instruction(std::string const & name,
                            std::string const & subtype);

    void global_variable_init(std::string const & name,
                              std::string const & type,
                              std::string const & value);

    void select_instruction(std::string const & dst,
                            std::string const & cond,
                            std::string const & sel1,
                            std::string const & sel2);

    bool conditional_branch_instruction(std::string const & condition,
                                        std::string const & joints);

    void cast_instruction(std::string const & src,
                          std::string const & dst,
                          std::string const & type,
                          bool const sext);

    void return_instruction(std::string const & return_name);

    void call_instruction(std::vector<std::string> const & oplist,
                          std::string const & returnto);

    void call_instruction_post(std::string const & fn_name,
                               std::string const & ret_type,
                               std::string const & caller);

    void begin_function(std::string const & function_name,
                        std::vector<std::string> const & oplist);

    void end_function();

    void begin_simulation();

    void end_simulation();

    void* function_pointer_hook(std::string const & fp_register);

    void memcpy(std::string const & addr_dst,
                std::string const & addr_src,
                std::string const & size_bytes,
                std::string const & align,
                std::string const & is_volatile);

    void memset(std::string const & addr_dst,
                std::string const & val,
                std::string const & len,
                std::string const & align,
                std::string const & _is_volatile);

    void getelementptr (std::string const & dst,
                        std::string const & pointer,
                        std::vector< std::string > const & indexes,
                        std::string const & offset_tree );

    void __YASSI_force_free(std::string const & variable,
                             unsigned long const size);

    void __YASSI_force_assertion(std::string const & _register);

    void __YASSI_debug(std::string const & message_register);

    void* __YASSI_malloc(std::string const & argument);

    void __YASSI_free(std::string const & variable);

private:
    void assign_instruction(Variables::BaseVariable* src_var,
                            Variables::BaseVariable* dst_var);
    void assign_function_pointer(Variables::BaseVariable* src_var,
                                 Variables::BaseVariable* dst_var);

    bool check_infinite_loop(z3::expr const & condition);

    void alloca_instruction_single(std::string const & name,
                                   std::string const & type);

    void call_instruction_post_instrumented(std::string const & function_name,
                                            std::string const & ret_type);
    void call_instruction_post_non_instrumented(std::string const & function_name,
                                                std::string const & ret_type);

    std::vector<Variables::BaseVariable*> p_function_call_arguments;
    std::list<std::string> p_function_return_register;   // The register beeing returned from the called function
    std::stack<std::string> p_caller_function_register;  // The register to assign the returned register from the function

    Yassi::Types::TypeFactory* p_type_factory;
    Memory* p_memory;
    Variables::VariableFactory* p_var_factory;
    Solver* p_problem;
    Propagation* p_propagation;
    Logger* p_logger;
    TypeCast* p_type_cast;
    CompareOperators* p_cmp_operators;
    ArithmeticOperators* p_arith_operators;
    PointerInstruction* p_pointer_instr;
    MemoryExporter* p_mem_export;
    LoadStore* p_load_store;
    ForceFree* p_force_free;
    Database* p_database;

    Variables::BaseVariable* p_malloc_obj;

    z3::context* p_z3_ctx;
    z3::solver* p_z3_slv;

    std::map<std::string, size_t> p_non_annotated_function_calls;

    std::list<z3::expr> p_last_assertions;

};

}

#endif /* YASSI_SYMBOLICEXECUTOR_HPP */
