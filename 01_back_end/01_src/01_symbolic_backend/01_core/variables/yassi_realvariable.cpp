/** 
 * @file yassi_realvariable.cpp
 * @brief Real Variable Type for Symbolic Execution
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
#include "yassi_realvariable.hpp"

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
RealVariable::RealVariable(BaseType* type,
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
RealVariable::~RealVariable() 
{
}

/**
 * @brief Return Existing SMT Instance owned by the Variable
 * 
 * @return z3::expr
 */
z3::expr RealVariable::get_formula_to_evaluate() 
{
    return p_smt_formula;
}

/**
 * @brief Return SMT Instance or create new SMT Instance if non existing
 * 
 * @return z3::expr
 */
z3::expr RealVariable::get_smt_formula() 
{
    size_t fraction = 0;
    size_t exponent = 0;
    
    if(this->get_type()->is_float()){
        FloatType* fp_type = dynamic_cast<FloatType*>(this->get_type());
        fraction = fp_type->get_fraction();
        exponent = fp_type->get_exponent();
    } else if (this->get_type()->is_double()) {
        DoubleType* db_type = dynamic_cast<DoubleType*>(this->get_type());
        fraction = db_type->get_fraction();
        exponent = db_type->get_exponent();
    } else {
        notimplemented_check();
    }
    
    if(p_obsolete_smt_formula){
        if(this->p_free_variable || this->p_force_free){ // Free Variable
            if(this->is_propaged_constant()){
                p_smt_formula = p_z3_ctx->fpa_const(this->get_propagated_from()->get_name().c_str(), exponent, fraction);
            } else {
                p_smt_formula = p_z3_ctx->fpa_const(this->get_name().c_str(), exponent, fraction);
            }
            p_obsolete_smt_formula = false;
        } else {
            if(this->get_type()->is_float()){
                float value = this->get_value_single_precision();
                p_smt_formula = p_z3_ctx->fpa_val(value);
            } else if (this->get_type()->is_double()){
                double value = this->get_value_double_precision();
                p_smt_formula = p_z3_ctx->fpa_val(value);
            } else {
                notsupported_check("Datatype not supported!");
            }
        }
    }
    return this->p_smt_formula; 
}

/**
 * @brief Dump Variable Content to give nstream
 * 
 * @param stream The stream to dump the information to
 */
void RealVariable::dump(std::ostream & stream) 
{
    stream << "---------------------------------" << std::endl;
    stream << "Name Hint: " << this->get_name_hint() << std::endl;
    stream << "Name : " << this->get_name() << std::endl;
    stream << "Value: " << this->get_value_as_string() << std::endl;
    stream << "Linear: " << this->get_is_linear() << std::endl;
    stream << "Propagated From: " << (p_propagated_from == nullptr ? "" : p_propagated_from->get_name())  << std::endl;
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
void RealVariable::set_pointer(BaseVariable* dst) 
{
    nullpointer_check(dst);
    notsupported_check("RealType is no pointer!");
}

/**
 * @brief Dereference Pointer
 * 
 * @return Yassi::Backend::Execute::BaseVariable*
 */
BaseVariable* RealVariable::get_pointer() 
{
    notsupported_check("RealType is no pointer!");
    exit(-1);
}
