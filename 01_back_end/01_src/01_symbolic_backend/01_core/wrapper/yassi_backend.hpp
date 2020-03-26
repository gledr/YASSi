/** 
 * @file yassi_backend.hpp
 * @brief Class Implementing the Backend Interface
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
#ifndef YASSI_BACKEND_HPP
#define YASSI_BACKEND_HPP

#include <yassi_object.hpp>
#include <yassi_database.hpp>
#include <yassi_symbolicexecutor.hpp>
#include <yassi_intrinsics.hpp>
#include <yassi_timer.hpp>
#include <yassi_callstack.hpp>
#include <yassi_baseutils.hpp>
#include <yassi_utils.hpp>
#include <yassi_z3utils.hpp>
#include <yassi_exception.hpp>

#include <signal.h>

extern "C" void yassi_global_init();

namespace Yassi::Backend::Execute {

/**
 * @class Backend
 * 
 * @brief This class represents the interface from LLVM IR World to Symbolic Execution
 * 
 * All Function calls performed by LLVM end up here as unsave C Strings, will be checked
 * for safety, mangled and forwared to symbolic execution for performing the requiered actions.
 */ 
class Backend : public virtual Object {
public:
    Backend ();

    virtual ~Backend ();
    
    void binary_op(char* _dst, char* _op1, char* _op2, char* _type, char* _line);
    void cast_instruction(char* dst, char* src, char* type, char* sext);
    void cmp_instr(char* dst, char* cmp1, char* cmp2, char* type);

    void load_instr(char* dst, char* dst_type, char* addr, char* line);
    void store_instr(char* addr, char* src, char* line);

    void alloca_instr(char* name, char* type);
    void global_var_init(char* _name, char* _type, char* _value);

    bool br_instr_cond(char* cond, char* joints);
    void br_instr_incond();

    void begin_bb(char * bb);
    void end_bb(char * bb);

    void begin_sim(char * source_file);
    void end_sim();

    void call_instr(char* _fn_name, char * oplist, char * ret_to);
    void return_instr(char* retname);
    void call_instr_post(char * fn_name, char * ret_type, char * caller);

    void begin_fn(char * _fn_name, char * _fn_oplist, char * _source_file);
    void end_fun();
    
    void select_op(char* _dst, char* _cond, char* _sel1, char* _sel2);
    void getelementptr(char* _dst, char* _pointer, char* _index, char* _offset_tree, char* _line);

    void memcpy(char* _addr_dst, char* _addr_src, char* _size_bytes, char* _align, char* _is_volatile);
    void memset(char* _addr_dst, char* _val, char* _len, char* _align, char* _is_volatile);

    void assume(char* _assumption_register);
    void assertion(char* _assertion_register, char* _line_num);

    void* fp_hook(char* _register_name);
    
    char nondet_char();
    int  nondet_int();
    unsigned int nondet_uint();
    bool nondet_bool();
    long nondet_long();
    void* nondet_pointer();

    void __YASSI_error(char* line_num);
    void __YASSI_force_free_local(char* _variable, unsigned long _size);
    void __YASSI_force_free_global(char * _variable, unsigned long _size);
    void __YASSI_force_assertion(char* variable);
    void __YASSI_debug(char* msg);
    
    void* __YASSI_malloc(char* argument);
    void __YASSI_free(char* variable_name);
    
    void alarm_handler();

private:
    SymbolicExecutor* p_sym_exec;
    Intrinsics* p_intrinsics;
    Timer* p_timer;
    Callstack* p_callstack;
    Logger* p_logger;
    Database* p_database;

    z3::context* p_z3_ctx;
    z3::solver* p_z3_slv;

    void options_from_db();
};

}

#endif /* YASSI_BACKEND_HPP */
