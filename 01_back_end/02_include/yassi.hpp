/** 
 * @file yassi.hpp
 * @brief Yassi Include Header to Access Intrinsic Functions
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
#ifndef YASSI_INTRINSICS_HPP
#define YASSI_INTRINSICS_HPP

#ifndef YASSI
#define YASSI
#endif

/**
 * @brief Force a variable to be free
 * 
 * The variable will be part of the SAT-Instance.
 * The function has to be called directly after the declaration in the C++ Code.
 * 
 * @param variable: The variable to be forced free.
 * @param size:     The number of bytes the variables takes
 */ 
void __YASSI_force_free_local(char * variable, unsigned long size);

/**
 * @brief Force a global variable to be free
 * 
 * The variable will be part of the SAT-Instance
 * The function has to be called in the C++ function which
 * first uses the function before usage (e.g. int main).
 * 
 * @param variable: The global variable to the free
 * @param size:     The number of bytes the variable takes
 */ 
void __YASSI_force_free_global(char* variable, unsigned long size);

/**
 * @brief Force a register to be true
 * 
 * @param variable: The variable holding the register name
 */
void __YASSI_force_assertion(char* variable);

/**
 * @brief Add an assumption to guide the result
 *
 * If the assumption is wrong, the SAT instance and the result
 * will be UNSAT, else the result will be guided.
 *
 * @param condition: The condition to guide the execution
 */
void __VERIFIER_assume(int condition);

/**
 * @brief Add an assertion to check properties
 */
void __VERIFIER_assert(int condition);

/**
 * @brief Function returns a non-deterministic character variable
 *
 * @return A non-deterministic character variable
 */
char __VERIFIER_nondet_char();

/**
 * @brief Function terminates execution and reports location where triggered
 */
void __VERIFIER_error();

/**
 * @brief Function returns a non-deterministic signed integer variable
 *
 * @return A non-deterministic signed integer variable
 */
int  __VERIFIER_nondet_int();

/**
 * @brief Function returns a non-deterministic unsigned integer variable
 *
 * @return A non-deterministic unsigned integer variable
 */
unsigned int __VERIFIER_nondet_uint();

/**
 * @brief Function returns a non-deterministic boolean variable
 *
 * @return A non-deterministic boolean variable
 */
bool __VERIFIER_nondet_bool();

/**
 * Function returns a non-deterministic signed long variable
 *
 * @return  A non-deterministic signed long variable
 */
long __VERIFIER_nondet_long();

/**
 * @brief Function returns a non-deterministic pointer
 *
 * @return A non-deterministic pointer
 */
void* __VERIFIER_nondet_pointer();

#endif /* YASSI_INTRINSICS_HPP */
