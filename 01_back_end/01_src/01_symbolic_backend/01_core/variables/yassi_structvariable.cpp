/** 
 * @file yassi_structvariable.cpp
 * @brief Struct Variable Type for Symbolic Execution
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
#include "yassi_structvariable.hpp"

using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;


/**
 * @brief Constructor
 * 
 * @param type Type Object of new Variable
 * @param name_hint Namehint of new Variable
 * @param constant Variable is Constant
 * @param z3_ctx Pointer to Z3 Context
 */
StructVariable::StructVariable(BaseType* type,
                               std::string const & name_hint,
                               bool const constant,
                               z3::context* z3_ctx):
    BaseVariable(z3_ctx)
{
    p_type = type;
    p_name_hint = name_hint;
    p_constant = constant;
}

/**
 * @brief Destructor
 */
StructVariable::~StructVariable() 
{
}

/**
 * @brief Return Existing SMT Instance owned by the Variable
 * 
 * @return z3::expr
 */
z3::expr StructVariable::get_formula_to_evaluate() 
{
    notsupported_check("Struct Variable must not command over an SMT Instance!");
    exit(-1);
}

/**
 * @brief Return SMT Instance or create new SMT Instance if non existing
 * 
 * @return z3::expr
 */
z3::expr StructVariable::get_smt_formula() 
{
    notsupported_check("StructVariable must not command over an SMT instance!!");
    exit(-1);
}

/**
 * @brief Dump Variable Content to give nstream
 * 
 * @param stream The stream to dump the information to
 */
void StructVariable::dump(std::ostream & stream) 
{
    stream << this->p_type->get_type_identifier() << std::endl;
    stream << this->get_name_hint() << std::endl;
    stream << this->get_smt_formula() << std::endl;
    stream << std::endl;
}

/**
 * @brief Set Pointer Variable
 * 
 * @param dst The Variable to Point to
 */
void StructVariable::set_pointer(BaseVariable* dst) 
{
    nullpointer_check(dst);
    notsupported_check("StructType is no pointer!");
}

/**
 * @brief Dereference Pointer
 * 
 * @return Yassi::Backend::Execute::BaseVariable*
 */
BaseVariable* StructVariable::get_pointer() 
{
    notsupported_check("StructType is no pointer!");
    exit(-1);
}
