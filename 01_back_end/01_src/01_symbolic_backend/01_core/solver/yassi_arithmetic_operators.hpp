/** 
 * @file yassi_arithmetic_operators.hpp
 * @brief This class realizes all arithmetic operations
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
#ifndef YASSI_ARITHMETIC_OPERATORS_HPP
#define YASSI_ARITHMETIC_OPERATORS_HPP

#include <cmath>

#include <yassi_object.hpp>
#include <yassi_variables.hpp>
#include <yassi_runtimeexception.hpp>

namespace Yassi::Backend::Execute {

/**
 * @class ArithmeticOperators
 * @brief This class realizes all arithmetic operations.
 *
 * All operations end up in an SMT instance and if linear dependent also 
 * direct calculated in order to minimize Solver Calls
 */
class ArithmeticOperators: public virtual Object {
public:

    ArithmeticOperators(z3::context* z3_ctx, z3::solver* z3_slv);

    virtual ~ArithmeticOperators();

    void calculate(Variables::BaseVariable* dst,
                   Variables::BaseVariable* op1,
                   Variables::BaseVariable* op2,
                   LLVMOpcode const & op);
    
private:
    z3::expr p_smt_result;
    z3::context* p_z3_ctx;
    z3::solver* p_z3_slv;
    std::string p_arith_result;

    RunTimeException* p_run_time_exception;

    void arith_pre(Variables::BaseVariable* dst,
                   Variables::BaseVariable* op1,
                   Variables::BaseVariable* op2);
    void arith_post(Variables::BaseVariable* dst,
                    Variables::BaseVariable* op1,
                    Variables::BaseVariable* op2);
    
    void int_add(Variables::BaseVariable* dst,
                 Variables::BaseVariable* op1,
                 Variables::BaseVariable* op2);
    void float_add(Variables::BaseVariable* dst,
                   Variables::BaseVariable* op1,
                   Variables::BaseVariable* op2);
    
    void int_sub(Variables::BaseVariable* dst,
                 Variables::BaseVariable* op1,
                 Variables::BaseVariable* op2);
    void float_sub(Variables::BaseVariable* dst,
                   Variables::BaseVariable* op1,
                   Variables::BaseVariable* op2);

    void int_mul(Variables::BaseVariable* dst,
                 Variables::BaseVariable* op1,
                 Variables::BaseVariable* op2);
    void float_mul(Variables::BaseVariable* dst,
                   Variables::BaseVariable* op1,
                   Variables::BaseVariable* op2);

    void int_signed_div(Variables::BaseVariable* dst,
                        Variables::BaseVariable* op1,
                        Variables::BaseVariable* op2);
    void int_unsigned_div(Variables::BaseVariable* dst,
                          Variables::BaseVariable* op1,
                          Variables::BaseVariable* op2);
    void float_div(Variables::BaseVariable* dst,
                   Variables::BaseVariable* op1,
                   Variables::BaseVariable* op2);

    void or_op(Variables::BaseVariable* dst,
               Variables::BaseVariable* op1,
               Variables::BaseVariable* op2);
    void and_op(Variables::BaseVariable* dst,
                Variables::BaseVariable* op1,
                Variables::BaseVariable* op2);
    void xor_op(Variables::BaseVariable* dst,
                Variables::BaseVariable* op1,
                Variables::BaseVariable* op2);

    void logic_shift_right(Variables::BaseVariable* dst,
                           Variables::BaseVariable* op1,
                           Variables::BaseVariable* op2);
    void arith_shift_right(Variables::BaseVariable* dst,
                           Variables::BaseVariable* op1,
                           Variables::BaseVariable* op2);
    void shift_left(Variables::BaseVariable* dst,
                    Variables::BaseVariable* op1,
                    Variables::BaseVariable* op2);
    
    void float_rem(Variables::BaseVariable* dst,
                   Variables::BaseVariable* op1,
                   Variables::BaseVariable* op2);
    void int_signed_rem(Variables::BaseVariable* dst,
                        Variables::BaseVariable* op1,
                        Variables::BaseVariable* op2);
    void int_unsigned_rem(Variables::BaseVariable* dst,
                          Variables::BaseVariable* op1,
                          Variables::BaseVariable* op2);

    bool is_unsigned(Variables::BaseVariable* op1,
                     Variables::BaseVariable* op2);
    void set_signed_unsigned(Variables::BaseVariable* dst,
                             Variables::BaseVariable* op1,
                             Variables::BaseVariable* op2);
    void set_unsigned(Variables::BaseVariable* dst,
                      Variables::BaseVariable* op1,
                      Variables::BaseVariable* op2);
    void set_signed(Variables::BaseVariable* dst,
                    Variables::BaseVariable* op1,
                    Variables::BaseVariable* op2);

    void arithmetic_exception_found(eException const what,
                                    std::string const & description = "");

    void check_integer_zero_division(Variables::BaseVariable* denominator);
    void check_real_zero_division(Variables::BaseVariable* denominator);

    void check_integer_zero_rem(Variables::BaseVariable* base);
    void check_real_zero_rem(Variables::BaseVariable* base);
};

}

#endif /* YASSI_ARITHMETIC_OPERATORS_HPP */
