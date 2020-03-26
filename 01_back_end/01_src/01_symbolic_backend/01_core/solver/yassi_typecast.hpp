/** 
 * @file yassi_typecast.hpp
 * @brief Class realizing Yassi's Typecasts
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
#ifndef YASSI_TYPECAST_HPP
#define YASSI_TYPECAST_HPP

#include <yassi_object.hpp>
#include <yassi_types.hpp>
#include <yassi_variables.hpp>
#include <yassi_variables.hpp>
#include <yassi_propagation.hpp>
#include <yassi_memory.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class TypeCast
 * @brief The class realizes all Typecasts as given by LLVM
 */
class TypeCast: public virtual Object{
public:
    TypeCast(z3::context * z3_ctx);

    virtual ~TypeCast();

    void cast_instruction(Variables::BaseVariable* src,
                          Variables::BaseVariable* dst,
                          bool const sext);

    void to_bool (Variables::IntegerVariable* src_var,
                  Variables::BoolVariable* dst_var );

    void from_bool (Variables::BoolVariable* src_var,
                    Variables::IntegerVariable* dst_var);

    void int_to_float(Variables::IntegerVariable* src_var,
    Variables::RealVariable* dst_var);

    void int_to_double(Variables::IntegerVariable* src_var,
                       Variables::RealVariable* dst_var);

    void double_to_int(Variables::RealVariable* src_var,
                       Variables::IntegerVariable* dst_var);

    void float_to_int(Variables::RealVariable* src_var,
                      Variables::IntegerVariable* dst_var);

    void extend_bitvector(Variables::IntegerVariable* src,
                          Variables::IntegerVariable* dst,
                          bool const sext);

    void extract_bitvector(Variables::BaseVariable* src,
                           Variables::BaseVariable* dst);
    
private:
    Propagation* p_propagation;
    Variables::VariableFactory* p_var_factory;
    Yassi::Types::TypeFactory* p_type_factory;
    Memory* p_memory;
    z3::context* p_z3_ctx;
};

}

#endif /* YASSI_TYPECAST_HPP */
