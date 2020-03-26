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
#ifndef YASSI_BACKEND_WRAPPER_HPP
#define YASSI_BACKEND_WRAPPER_HPP

#include "yassi_backend.hpp"

#include <signal.h>

/**
 * @brief Called when a binary operation is performed among two variables
 *
 * @param _dst: Destination name
 * @param _op1: First operand name
 * @param _op2: Second operand name
 * @param _operation: Operation kind
 * @param _line: Location in Source File
 */
extern "C" void __YASSI_binary_op(char* _dst, char* _op1, char* _op2, char* _operation, char* _line);

/**
 * @brief Called when a cast instruction is performed
 *
 * @param _dst: Name of the destination register
 * @param _src: Name of the source register
 * @param _type: Type of the destination data
 */
extern "C" void __YASSI_cast_instruction(char* _dst, char* _src, char* _type, char* _sext);

/**
 * @brief Called when a load instruction assigns the value of a memory position (pointed by the register named addr) to a register
 *
 * @param _dst: name of the destination register
 * @param _dst_type: type of the destination register
 * @param _addr: name of the register that contains the address
 * @param _line: line of code from the load_instr
 */
extern "C" void __YASSI_load_instr(char* _dst, char* _dst_type, char* _addr, char* _line);

/**
 * @brief Called when a store instruction assigns the value of a register to a memory position
 *
 * @param _src: register name
 * @param _addr: name of the register that contains the address of the store
 * @param _line: liste of code of the store_instr
 */
extern "C" void __YASSI_store_instr(char* _src, char* _addr, char* _line);

/**
 * @brief Comparison instruction
 *
 * @param _dst: name of the destination
 * @param _cmp1: Name of the first register
 * @param _cmp2: Name of the second register
 * @param _type: Type of comparison
 */
extern "C" void __YASSI_cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type);

/**
 * @brief Conditional branch instruction
 *
 * @param _cmp: Name of the register that contains the branch condition
 *
 * @return 
 */
extern "C" bool __YASSI_br_instr_cond(char*, char*);

/**
 * @brief Inconditional branch instruction
 */
extern "C" void __YASSI_br_instr_incond();

/**
 * @brief  Begin basic Block
 *
 * @param name: Name of the basic block
 */
extern "C" void __YASSI_begin_bb(char* a);

/**
 * @brief End basic block
 *
 * @param name
 */
extern "C" void __YASSI_end_bb(char* a);

/**
 * @brief Function that is called when a new variable is allocated
 *
 * @param _reg: name of the register that holds the position of new variable in memory
 * @param _type: Data type of allocated value
 */
extern "C" void __YASSI_alloca_instr(char* _reg, char* _type);

/**
 * @brief Function that is called at the begining of simulation
 */
extern "C" void __YASSI_begin_sim(char* source_file);

/**
 * @brief Function that is called at the end of simulation
 */
extern "C" void __YASSI_end_sim();

/**
 * @brief Called when a getelementptr operation is performed
 *
 * @param _dst: Destination register with the calculated offset
 * @param _pointer: Source pointer
 * @param _indexes: Indexes with the values to be accessed
 * @param _offset_tree: Tree containing the offset of each index
 * @param _line:
 */
extern "C" void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree, char* _line);

/**
 * @brief Called to initialize a global variable
 *
 * @param _name: Name of the global variable
 * @param _type: Type
 * @param _value: Values to be initialized
 */
extern "C" void global_var_init(char* _name, char* _type, char* _value);

/**
 * @brief Function to instrument a function call
 *
 * @param _fn_name: Name of the called function
 * @param _oplist: Actual parameters
 * @param _ret_to
 */
extern "C" void __YASSI_call_instruction (char* _fn_name, char* _oplist, char* _ret_to);

/**
 * @brief 
 * 
 * @param _fn_name:
 * @param _ret_type:
 * @param _caller:
 */
extern "C" void __YASSI_call_instruction_post( char* _fn_name, char* _ret_type, char* _caller );

/**
 * @brief
 * 
 * @param _retname:
 */
extern "C" void __YASSI_return_instruction(char* _retname);

/**
 * @brief Indicates that the execution of a particular function has been started.
 * 
 * @param _fn_name: The name of the function.
 * @param _fn_oplist: The arguments of the called function.
 * @param _source_file: The source file where the function is located.
 */
extern "C" void __YASSI_begin_fn(char* _fn_name, char* _fn_oplist, char* _source_file);

/**
 * @brief Indicates that the function being executed has been finished.
 */
extern "C" void __YASSI_end_fn();

/**
 * @brief Boolean If-Then-Else Select Operator
 * 
 * Function: _dest = _cond ? _sel1 : _sel2
 * 
 * @param _dest: The register to write the result
 * @param _cond: The boolean condition
 * @param _sel1: Result for true condition
 * @param _sel2: Result for false condition
 */
extern "C" void __YASSI_select_op(char* _dest, char* _cond, char* _sel1, char* _sel2 );

/**
 * @brief Instrinsic LLVM Memory Copy. Copy Memory from _addr_src to _addr_dst
 * 
 * @param _addr_dst: The Memory Location to Copy to.
 * @param _addr_src: The Memory Location to Copy from.
 * @param _size_bytes: The bytes to copy in total.
 * @param _align: The memory alignment of the memory.
 * @param _is_volatile: Memory region is volatile or not.
 */
extern "C" void __YASSI_memcpy(char * _addr_dst, char * _addr_src, char * _size_bytes, char * _align, char * _is_volatile);

/**
 * @brief Instrincit LLVM Memory Set. Set a particular Memory Region.
 * 
 * @param _addr_dst: Beginning of the memory region to set.
 * @param _val: Value to be used.
 * @param _len: Lenght of the Memory to be set.
 * @param _align: Memory alignment of the memory.
 * @param _is_volatile: Memory region is volatile or not.
 */
extern "C" void __YASSI_memset(char * addr_dst, char * val, char * len, char * _align, char * _is_volatile);

/**
 * @brief Write to stdout
 * 
 * @param _msg: The message to dump
 */ 
extern "C" int __YASSI_debug(char* _msg);

/**
 * @brief
 * 
 * @param _register_with_fp
 * @return void*
 */
extern "C" void* fp_hook(char* _register_with_fp);

/**
 * @brief
 * 
 * @param _line_num:
 */
extern "C" void __YASSI_error(char* _line_num);

/**
 * @brief
 * 
 * @param _assumption_register:
 */
extern "C" void __YASSI_assume(char* _assumption_register);

/**
 * @brief
 * 
 * @param _assertion_register:
 * @param _line:
 */
extern "C" void __YASSI_assert(char* _assertion_register, char* _line);


/**
 * @brief
 * @param _assertion_register:
 */
extern "C" void __YASSI_force_assertion(char* _assertion_register);

/**
 * @brief Allocate Memory on the Heap
 * 
 * @param argument: Number of Bytes
 */
extern "C" void* __YASSI_malloc(char* argument);

/**
 * @brief Release Memory on the Heap
 * 
 * @param _variable_name: Variable holding the Memory
 */
extern "C" void __YASSI_free(char* _variable_name);

/**
 * @brief
 * 
 * @param signal:
 */
void alarm_handler(int signal);

#include <yassi.hpp>

#endif /* YASSI_BACKEND_WRAPPER_HPP */
