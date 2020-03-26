/** 
 * @file yassi_variablefactory.cpp
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
#include "yassi_variablefactory.hpp"

using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 * 
 * @param z3_ctx: Z3 Context of the new variables
 */
VariableFactory::VariableFactory(z3::context* z3_ctx):
    Object(), p_z3_ctx(z3_ctx)
{
    nullpointer_check(z3_ctx);

    p_type_factory = new TypeFactory();
}

/**
 * @brief Destructor
 */
VariableFactory::~VariableFactory() 
{
    delete p_type_factory; p_type_factory = nullptr;
}

/**
 * @brief Create a new constant variable from identifier string
 * 
 * @param identifier: Identifier string of the new constant variable
 * @return Yassi::BaseVariable*
 */
BaseVariable* VariableFactory::create_variable_from_constant(std::string const & identifier) 
{
    check_namemangling(identifier);

    std::vector<std::string> token = BaseUtils::tokenize(identifier, NameMangling::MANGELING_SEPERATOR);

    BaseVariable* tmp_var = this->create_variable(identifier, token[1], true);
    tmp_var->set_is_linear(true);
    
    if(!tmp_var->get_type()->is_void()){
        tmp_var->set_value(token[2]);
    }
    return tmp_var;
}

/**
 * @brief Create a new IntegerVariable from scratch
 * 
 * @param type:         Type of the new variable
 * @param name_hint:    Name hint of the new variable
 * @param constant:     New variable is constant or not
 * @return Yassi::IntegerVariable*
 */
IntegerVariable* VariableFactory::create_integer_variable(BaseType* const type,
                                                          std::string const & name_hint,
                                                          bool const constant) 
{
    nullpointer_check(type);

    IntegerVariable* tmp = new IntegerVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<IntegerVariable>(tmp);

    return tmp;
}

/**
 * @brief Create a new RealVariable from scratch
 * 
 * @param type:         Type of the new variable
 * @param name_hint:    Name hint of the new variable
 * @param constant:     New variable is constant or not
 * @return Yassi::RealVariable*
 */
RealVariable* VariableFactory::create_real_variable(BaseType* const type,
                                                    std::string const & name_hint,
                                                    bool const constant) 
{
    nullpointer_check(type);

    RealVariable* tmp = new RealVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<RealVariable>(tmp);

    return tmp;
}

/**
 * @brief Create a new BoolVariable from scratch
 * 
 * @param type:         Type of the new variable
 * @param name_hint:    Name hint of the new variable
 * @param constant:     New variable is constant or not
 * @return Yassi::BoolVariable*
 */
BoolVariable* VariableFactory::create_bool_variable(BaseType* const type,
                                                    std::string const & name_hint,
                                                    bool const constant) 
{
    nullpointer_check(type);

    BoolVariable* tmp = new BoolVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<BoolVariable>(tmp);

    return tmp; 
}

/**
 * @brief Create a new PointerVariable from scratch
 * 
 * @param type:         Type of the new variable
 * @param name_hint:    Name hint of the new variable
 * @param constant:     New variable is constant or not
 * @return Yassi::PointerVariable*
 */
PointerVariable* VariableFactory::create_pointer_variable(BaseType* const type,
                                                          std::string const & name_hint,
                                                          bool const constant)
{
    nullpointer_check(type);

    PointerVariable* tmp = new PointerVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<PointerVariable>(tmp);

    return tmp;
}

/**
 * @brief Create a new VoidVariable from scratch
 * 
 * @param type:         Type of the new variable
 * @param name_hint:    Name hint of the new variable
 * @param constant:     New variable is constant or not
 * @return Yassi::VoidVariable*
 */
VoidVariable* VariableFactory::create_void_variable(BaseType* const type,
                                                    std::string const & name_hint,
                                                    bool const constant)
{
    nullpointer_check(type);

    VoidVariable* tmp = new VoidVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<VoidVariable>(tmp);

    return tmp;
}

/**
 * @brief Create a new StructVariable from scratch
 * 
 * @param type:         Type of the new variable
 * @param name_hint:    Name hint of the new variable
 * @param constant:     New variable is constant or not
 * @return Yassi::StructVariable*
 */
StructVariable* VariableFactory::create_struct_variable(BaseType* const type,
                                                        
                                                        std::string const & name_hint,
                                                        bool const constant)
{
    nullpointer_check(type);

    StructVariable* tmp = new StructVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<StructVariable>(tmp);

    return tmp;
}

/**
 * @brief Create a new ArrayVariable from scratch
 * 
 * @param type:         Type of the new variable
 * @param name_hint:    Name hint of the new variable
 * @param constant:     New variable is constant or not
 * @return Yassi::ArrayVariable*
 */
ArrayVariable* VariableFactory::create_array_variable(BaseType* const type,
                                                      std::string const & name_hint,
                                                      bool const constant)
{
    nullpointer_check(type);

    ArrayVariable* tmp = new ArrayVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<ArrayVariable>(tmp);

    return tmp;
}

/**
 * @brief Create a new FuntionVariable from scratch
 * 
 * @param type:       Type of the new variable
 * @param name_hint:  Name hint of the new variable
 * @param constant:   New variable is constant or not
 * @return Yassi::FunctionVariable*
 */
FunctionVariable* VariableFactory::create_function_variable(BaseType* const type,
                                                            std::string const & name_hint,
                                                            bool const constant)
{
    nullpointer_check(type);

    FunctionVariable* tmp = new FunctionVariable(type, name_hint, constant, p_z3_ctx);
    this->set_entironment<FunctionVariable>(tmp);

    return tmp;
}

/**
 * @brief Create a new Polymorph Variable
 * 
 * @param name:     The name hint of the new variable
 * @param type:     The type of the new variable
 * @param constant: New Variable is constant or not
 * @return Yassi::BaseVariable*
 */
BaseVariable* VariableFactory::create_variable(std::string const name,
                                               std::string const type,
                                               bool const constant)
{
    BaseType* type_obj = p_type_factory->get_type_by_identifier(type);

    if(type_obj->is_integer_class()){
        return this->create_integer_variable(type_obj, name, constant);
    } else if (type_obj->is_real_class()){
        return this->create_real_variable(type_obj, name, constant);
    } else if (type_obj->is_bool_class()){
        return this->create_bool_variable(type_obj, name, constant);
    } else if (type_obj->is_pointer()) {
        return this->create_pointer_variable(type_obj, name, constant);
    } else if (type_obj->is_void()){
        return this->create_void_variable(type_obj, name, constant);
    } else if (type_obj->is_struct()){
        return this->create_struct_variable(type_obj, name, constant);
    } else if (type_obj->is_function()){
        return this->create_function_variable(type_obj, name, constant);
    } else if (type_obj->is_array()){
        return this->create_array_variable(type_obj, name, constant);
    } else {
        notimplemented_check();
        exit(-1);
    }
}

/*
 * @brief Set the environment for every variable
 * 
 * @param var: Template type for Polymorph BaseVariables
 */ 
template<typename T> 
void VariableFactory::set_entironment(T* var)
{
    nullpointer_check(var);

    var->set_sourcefile(this->get_file_being_executed());
    var->set_function(this->get_current_function());
}
