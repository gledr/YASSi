/** 
 * @file yassi_compare_operators.hpp
 * @brief This class realizes all compare operations
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
#ifndef YASSI_COMPARE_OPERATORS_HPP
#define YASSI_COMPARE_OPERATORS_HPP

#include <yassi_object.hpp>
#include <yassi_variables.hpp>
#include <yassi_llvm_enums.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

std::string const ERRMSG_INTEQ = "Compare Operation: Integer Equal ";

/**
 * @class CompareOperators
 * @brief This class realizes all compare operations.
 *
 * All operations end up in an SMT instance and if linear dependent also 
 * direct calculated in order to minimize Solver Calls
 */
class CompareOperators: public virtual Object {
public:

    CompareOperators(z3::context* z3_ctx);

    virtual ~CompareOperators();

    void compare(Variables::BaseVariable* dst,
                 Variables::BaseVariable* op1,
                 Variables::BaseVariable* op2,
                 int const & op);

private:
    z3::expr p_smt_result;
    z3::context* p_z3_ctx;
    std::string p_logic_result;

    bool is_unsigned(Variables::BaseVariable* op1,
                     Variables::BaseVariable* op2);
    void set_signed_unsigned(Variables::BaseVariable* dst,
                             Variables::BaseVariable* op1,
                             Variables::BaseVariable* op2);

    void compare_pre(Variables::BaseVariable* dst,
                     Variables::BaseVariable* op1,
                     Variables::BaseVariable* op2);
    void compare_post(Variables::BaseVariable* dst,
                      Variables::BaseVariable* op1,
                      Variables::BaseVariable* op2);

    void set_unsigned(Variables::BaseVariable* dst,
                      Variables::BaseVariable* op1,
                      Variables::BaseVariable* op2);
    void set_signed(Variables::BaseVariable* dst,
                    Variables::BaseVariable* op1,
                    Variables::BaseVariable* op2);

    void compare_integer(Variables::BaseVariable* dst_var,
                         Variables::BaseVariable* var_op1,
                         Variables::BaseVariable* var_op2,
                         LLVMIntPredicate const & op);
    void compare_real(Variables::BaseVariable*  dst_var,
                      Variables::BaseVariable* var_op1,
                      Variables::BaseVariable* var_op2,
                      LLVMRealPredicate const & op);

    void integer_equal(Variables::BaseVariable* dst,
                       Variables::BaseVariable* op1,
                       Variables::BaseVariable* op2);
    void integer_unequal(Variables::BaseVariable* dst,
                         Variables::BaseVariable* op1,
                         Variables::BaseVariable* op2);

    void integer_signed_greater_equal(Variables::BaseVariable* dst,
                                      Variables::BaseVariable* op1,
                                      Variables::BaseVariable* op2);
    void integer_signed_greater_than(Variables::BaseVariable* dst,
                                     Variables::BaseVariable* op1,
                                     Variables::BaseVariable* op2);

    void integer_signed_less_than(Variables::BaseVariable* dst,
                                  Variables::BaseVariable* op1,
                                  Variables::BaseVariable* op2);
    void integer_signed_less_equal(Variables::BaseVariable* dst,
                                   Variables::BaseVariable* op1,
                                   Variables::BaseVariable* op2);

    void integer_unsigned_greater_than(Variables::BaseVariable* dst,
                                       Variables::BaseVariable* op1,
                                       Variables::BaseVariable* op2);
    void integer_unsigned_greater_equal(Variables::BaseVariable* dst,
                                        Variables::BaseVariable* op1,
                                        Variables::BaseVariable* op2);

    void integer_unsigned_less_than(Variables::BaseVariable* dst,
                                    Variables::BaseVariable* op1,
                                    Variables::BaseVariable* op2);
    void integer_unsigned_less_equal(Variables::BaseVariable* dst,
                                     Variables::BaseVariable* op1,
                                     Variables::BaseVariable* op2);

    void real_equal(Variables::BaseVariable* dst,
                    Variables::BaseVariable* op1,
                    Variables::BaseVariable* op2);
    void real_unequal(Variables::BaseVariable* dst,
                      Variables::BaseVariable* op1,
                      Variables::BaseVariable* op2);

    void real_greater_than(Variables::BaseVariable* dst,
                           Variables::BaseVariable* op1,
                           Variables::BaseVariable* op2);
    void real_greater_equal(Variables::BaseVariable* dst,
                            Variables::BaseVariable* op1,
                            Variables::BaseVariable* op2);

    void real_less_than(Variables::BaseVariable* dst,
                        Variables::BaseVariable* op1,
                        Variables::BaseVariable* op2);
    void real_less_equal(Variables::BaseVariable* dst,
                         Variables::BaseVariable* op1,
                         Variables::BaseVariable* op2);
};

}

#endif /* YASSI_COMPARE_OPERATORS_HPP */
