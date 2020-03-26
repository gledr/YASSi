/** 
 * @file yassi_variablefactory.hpp
 * @brief Factory Class for Variables
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
#ifndef YASSI_VARIABLEFACTORY_HPP
#define YASSI_VARIABLEFACTORY_HPP

#include <vector>
#include <z3++.h>

#include <yassi_object.hpp>
#include <yassi_integervariable.hpp>
#include <yassi_realvariable.hpp>
#include <yassi_boolvariable.hpp>
#include <yassi_pointervariable.hpp>
#include <yassi_voidvariable.hpp>
#include <yassi_structvariable.hpp>
#include <yassi_functionvariable.hpp>
#include <yassi_arrayvariable.hpp>
#include <yassi_typefactory.hpp>
#include <yassi_utils.hpp>
#include <yassi_namemangling.hpp>

namespace Yassi::Backend::Execute::Variables {

/**
 * @class VariableFactory
 * @brief Factory for Variable Instances
 */
class VariableFactory: public virtual Object {
public:
    VariableFactory(z3::context* z3_ctx);

    virtual ~VariableFactory();

    BaseVariable * create_variable_from_constant(std::string const & identifier);

    BaseVariable * create_variable(std::string const name,
                                   std::string const type,
                                   bool const constant = false);

    IntegerVariable* create_integer_variable(Yassi::Types::BaseType* const type,
                                             std::string const & name_hint,
                                             bool const constant = false);

    BoolVariable* create_bool_variable(Yassi::Types::BaseType* const type,
                                       std::string const & name_hint,
                                       bool const constant = false);

    RealVariable* create_real_variable(Yassi::Types::BaseType* const type,
                                       std::string const & name_hint,
                                       bool const constant = false);

    PointerVariable* create_pointer_variable(Yassi::Types::BaseType* const type,
                                             std::string const & name_hint,
                                             bool const constant = false);

    VoidVariable* create_void_variable (Yassi::Types::BaseType*const type,
                                        std::string const & name_hint,
                                        bool const constant = false);

    StructVariable* create_struct_variable(Yassi::Types::BaseType* const type,
                                           std::string const & name_hint,
                                           bool const constant = false);

    FunctionVariable* create_function_variable(Yassi::Types::BaseType* const type,
                                               std::string const & name_hint,
                                               bool const constant = false);

    ArrayVariable* create_array_variable(Yassi::Types::BaseType* const type,
                                         std::string const & name_hint,
                                         bool const constant = false);

private:

    template <typename T>
    void set_entironment(T* var);

    Yassi::Types::TypeFactory* p_type_factory;

    z3::context * p_z3_ctx;
};

}

#endif /* YASSI_VARIABLEFACTORY_HPP */
