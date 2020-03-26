/** 
 * @file yassi_pointervariable.cpp
 * @brief Pointer Variable Type for Symbolic Execution
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
#include "yassi_pointervariable.hpp"

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
PointerVariable::PointerVariable(BaseType* type,
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
PointerVariable::~PointerVariable()
{
}

/**
 * @brief Return Existing SMT Instance owned by the Variable
 * 
 * @return z3::expr
 */
z3::expr PointerVariable::get_formula_to_evaluate() 
{
   return p_smt_formula;
}

/**
 * @brief Return SMT Instance or create new SMT Instance if non existing
 * 
 * @return z3::expr
 */
z3::expr PointerVariable::get_smt_formula() 
{
     if(p_obsolete_smt_formula){
        if(this->p_free_variable || this->p_force_free){ // Free Variable
            if(this->is_propaged_constant()){
                p_smt_formula = p_z3_ctx->bv_const(this->get_propagated_from()->get_name().c_str(), this->p_type->get_bits());
            } else {
                p_smt_formula = p_z3_ctx->bv_const(this->get_name().c_str(), this->p_type->get_bits());
            }
        } else {
            std::string value = this->get_value_as_string();
            p_smt_formula = p_z3_ctx->bv_val(std::stoi(value), this->p_type->get_bits());
        }
        p_obsolete_smt_formula = false;
    }
    return this->p_smt_formula; 
}

/**
 * @brief Dump Variable Content to give nstream
 * 
 * @param stream The stream to dump the information to
 */
void PointerVariable::dump(std::ostream & stream) 
{
    stream << "---------------------------------" << std::endl;
    stream << "Name Hint: " << this->get_name_hint() << std::endl;
    stream << "Name : " << this->get_name() << std::endl;
    stream << "Value: " << this->get_value_as_string() << std::endl;
    if(this->get_pointer() != nullptr){
        stream << "Pointer: " << this->get_pointer()->get_name() << " (" << this->get_pointer()->get_type()->get_type_identifier() << ")" << std::endl;
    } else {
        stream << "Pointer: NULL" << std::endl;
    }
    stream << "Comes From Non Annotated: " << this->get_comes_from_nonannotated() << std::endl;
    stream << "Propagated From: " << (p_propagated_from == nullptr ? "" : p_propagated_from->get_name()) << std::endl;
    stream << "Type: " << p_type->get_type_identifier() << std::endl;
    stream << "First Address: " << p_firstaddress << " Lass Address: " << p_lastaddress << std::endl;
    stream << "SMT2: " << this->get_smt_formula() << std::endl;
    stream << "Free: " << this->is_free_variable() << std::endl;
    stream << "ForcedFree: " << this->is_forced_free() << std::endl;
    stream << "---------------------------------" << std::endl;
}

/**
 * @brief Set Pointer Variable
 * 
 * @param dst The Variable to Point to
 */
void PointerVariable::set_pointer(BaseVariable* dst) 
{
    if(dst != nullptr){
        this->unset_free_variable();
    }
    this->p_pointer = dst;
}

/**
 * @brief Dereference Pointer
 * 
 * @return Yassi::Backend::Execute::BaseVariable*
 */
BaseVariable* PointerVariable::get_pointer() 
{
    return p_pointer;
}
