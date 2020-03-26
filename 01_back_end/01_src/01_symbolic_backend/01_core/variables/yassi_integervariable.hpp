/** 
 * @file yassi integervariable.hpp
 * @brief Integer Variable Type for Symbolic Execution
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
#ifndef YASSI_INTEGERVARIABLE_HPP
#define YASSI_INTEGERVARIABLE_HPP

#include "yassi_basevariable.hpp"

namespace Yassi::Backend::Execute::Variables {

class VariableFactory;

/**
 * @class IntegerVariable
 * @brief Integer Variable Type for Symbolic Execution
 */
class IntegerVariable: public BaseVariable {
public:
    virtual ~IntegerVariable();

    virtual z3::expr get_smt_formula();

    virtual z3::expr get_formula_to_evaluate();

    virtual void dump(std::ostream & stream = std::cout); 

    virtual void set_pointer(BaseVariable* dst);

    virtual BaseVariable* get_pointer();

private:
    friend class VariableFactory;

    IntegerVariable(Yassi::Types::BaseType* type,
                    std::string const & name_hint,
                    bool const constant = false,
                    z3::context* z3_ctx = nullptr);
};

}

#endif /* YASSI_INTEGERVARIABLE_HPP */
