/** 
 * @file yassi_backend_wrapper.hpp
 * @brief Interface to the Execution Backend Library
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
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
#include "yassi_backend_wrapper.hpp"

using namespace Yassi::Backend::Execute;


Backend* p_backend;
bool p_active_simulation = false;

void __YASSI_cast_instruction(char* _dst, char* _src, char* _type, char* _sext)
{    
    if(p_active_simulation){
        p_backend->cast_instruction(_dst, _src, _type, _sext);
    }
}

void __YASSI_call_instruction_post(char* _fn_name, char* _ret_type, char* _caller)
{
    if(p_active_simulation){
        p_backend->call_instr_post(_fn_name, _ret_type, _caller);
    }
}

void __YASSI_call_instruction(char* _fn_name, char* _oplist, char* _ret_to)
{
    if(p_active_simulation){
        p_backend->call_instr(_fn_name, _oplist, _ret_to);
    }
}

void __YASSI_select_op(char* _dest, char* _cond, char* _sel1, char* _sel2)
{
    if(p_active_simulation){
        p_backend->select_op(_dest, _cond, _sel1, _sel2);
    }
}

void __YASSI_return_instruction(char* _retname)
{
    if(p_active_simulation){
        p_backend->return_instr(_retname);
    }
}

void __YASSI_binary_op(char* _dst, char* _op1, char* _op2, char* _operation, char *_line)
{
    if(p_active_simulation){
        p_backend->binary_op(_dst, _op1, _op2, _operation, _line);
    }
}

void __YASSI_load_instr(char* _dst, char* _dst_type, char* _addr, char* _line)
{
    if(p_active_simulation){
        p_backend->load_instr(_dst, _dst_type, _addr, _line);
    }
}

void __YASSI_store_instr(char* _src, char* _addr, char* _line)
{
    if(p_active_simulation){
        p_backend->store_instr(_src, _addr, _line);
    }
}

void __YASSI_cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type)
{
    if(p_active_simulation){
        p_backend->cmp_instr(_dst, _cmp1, _cmp2, _type);
    }
}

void __YASSI_br_instr_incond()
{
    if(p_active_simulation){
        p_backend->br_instr_incond();
    }
}

void __YASSI_begin_bb(char* _name)
{
    if(p_active_simulation){
        p_backend->begin_bb(_name);
    }
}

void __YASSI_end_bb(char* _name)
{
    if(p_active_simulation){
        p_backend->end_bb(_name);
    }
}

void global_var_init(char* _varname, char* _type, char* _value)
{
    if(p_active_simulation){
        p_backend->global_var_init(_varname, _type, _value);
    }
}

void __YASSI_alloca_instr(char* _reg, char* _type)
{
    if(p_active_simulation){
        p_backend->alloca_instr(_reg, _type);
    }
}

void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree, char* _line)
{
    if(p_active_simulation){
        p_backend->getelementptr(_dst, _pointer, _indexes, _offset_tree, _line);
    }
}

void __YASSI_begin_sim(char* source_file)
{
    p_backend = new Backend();
    
    if(signal(SIGALRM, alarm_handler) == SIG_ERR){
        perror("Can not activate handler for SIGALRM\n");
    }
    if(setpgid(getpid(), getpid() == 1)){
        perror("Can not configure Process Group ID\n");
    }
    p_active_simulation = true;
    p_backend->begin_sim(source_file);
    yassi_global_init();
}

void __YASSI_begin_fn(char* _fn_name, char* _fn_oplist, char* _source_file)
{
    if(p_active_simulation){
        p_backend->begin_fn(_fn_name, _fn_oplist, _source_file);
    }
}

void __YASSI_end_fn() 
{
    if(p_active_simulation){
        p_backend->end_fun();
    }
}

void __YASSI_end_sim()
{
    p_active_simulation = false;
    p_backend->end_sim();

    delete p_backend; p_backend = nullptr;
}

bool __YASSI_br_instr_cond(char* _cmp, char* _joints)
{   
    if(p_active_simulation){
        return p_backend->br_instr_cond(_cmp, _joints);
    } else {
        return false;
    }
}

void __YASSI_assume(char* _assumption_register)
{
    if(p_active_simulation){
        p_backend->assume(_assumption_register);
    }
}

void __YASSI_assert(char* _assertion_register, char* _line_num)
{
    if(p_active_simulation){
        p_backend->assertion(_assertion_register, _line_num);
    }
}

void __YASSI_memcpy(char * addr_dst, char * addr_src, char * size_bytes, char * _align, char * _is_volatile)
{
    if(p_active_simulation){
        p_backend->memcpy(addr_dst, addr_src, size_bytes, _align, _is_volatile);
    }
}

void __YASSI_memset(char * addr_dst, char * val, char * len, char * _align, char * _is_volatile)
{
    if(p_active_simulation){
        p_backend->memset(addr_dst, val, len, _align, _is_volatile);
    }
}

void* fp_hook(char* _register_with_fp)
{
    if(p_active_simulation){
        return p_backend->fp_hook(_register_with_fp);
    } else {
        return nullptr;
    }
}

void __YASSI_error(char* _line_num)
{
    p_backend->__YASSI_error(_line_num);
}

int  __VERIFIER_nondet_int() 
{
    return p_backend->nondet_int();
}

char __VERIFIER_nondet_char() 
{
    return p_backend->nondet_char();
}

unsigned int __VERIFIER_nondet_uint() 
{
    return p_backend->nondet_uint();
}

bool __VERIFIER_nondet_bool()
{
    return p_backend->nondet_bool();
}

long __VERIFIER_nondet_long()
{
    return p_backend->nondet_long();
}

void* __VERIFIER_nondet_pointer()
{
    return p_backend->nondet_pointer();
}

void __YASSI_force_free_local(char * variable_name, unsigned long size)
{
    p_backend->__YASSI_force_free_local(variable_name, size);
}

void __YASSI_force_free_global(char* variable_name, unsigned long size)
{
    p_backend->__YASSI_force_free_global(variable_name, size);
}

void __YASSI_force_assertion(char * variable)
{
    if(p_active_simulation){
        p_backend->__YASSI_force_assertion(variable);
    }
}

int __YASSI_debug(char* msg)
{
    p_backend->__YASSI_debug(msg);

    return 0;
}

void* __YASSI_malloc(char* argument)
{
    p_backend->__YASSI_malloc(argument);
}

void __YASSI_free(char* variable)
{
    p_backend->__YASSI_free(variable);
}

void alarm_handler(int signal)
{
    assert (signal == SIGALRM);
    p_backend->alarm_handler();
}
