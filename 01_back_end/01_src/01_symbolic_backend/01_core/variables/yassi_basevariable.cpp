/** 
 * @file yassi_basevariable.cpp
 * @brief Virtual Base Variable Type for Symbolic Execution
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
#include "yassi_basevariable.hpp"

using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Types;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 * 
 * @param z3_ctx Z3 Context
 */
BaseVariable::BaseVariable(z3::context* z3_ctx):
    p_smt_formula(z3_ctx->bool_val("0")), p_index_assertion(z3_ctx->bool_val("0"))
{
    nullpointer_check(z3_ctx);
    
    p_z3_ctx = z3_ctx;
    p_free_variable = true;
    p_force_free = false;
    p_linear = false;
    p_value = "0";
    p_sign = eUnknown;
    p_lastaddress = 0;
    p_firstaddress = 0;
    p_alloc_point = 999;
    propageted_constant = false;
    p_propagated_from = nullptr;
    p_pointer = nullptr;
    p_parent = nullptr;
    p_comes_from_nonannotated = false;
    p_function_pointer = false;
    p_obsolete_smt_formula = true;
    p_has_index_assertion = false;
    p_allocation_type = eUnallocated;
    p_global = false;
    p_constant = false;
}

/**
 * @brief Destructor
 */
BaseVariable::~BaseVariable()
{
}

/**
 * @brief Set the unique name of the variable.
 *
 * @param name: The unique name to be used.
 */
void BaseVariable::set_name(std::string const & name)
{
    p_name = name;
}

/**
 * @brief Get the unique name of the variable.
 *
 * @return The unique name used for the variable.
 */
std::string BaseVariable::get_name()
{
    return p_name;
}

/**
 * @brief Set the name hint stored for a variable.
 * The name hint refers to the name used for the variable 
 * in the C/C++ code. Name hint is not unique!
 * 
 * @param hint: The hint to store for the variable.
 */
void BaseVariable::set_name_hint(std::string const & hint)
{
    p_name_hint = hint;
}

/**
 * @brief Get the name hint stored for the variable.
 * The name hint refers to the name used for the variable
 * in the C/C++ code. Name hint is not unique!
 *
 * @return The stored name hint for the variable.
 */
std::string BaseVariable::get_name_hint() 
{
    return p_name_hint;
}

/**
 * @brief Shows if the variable is classified as free variable.
 *
 * @return The stored classification information.
 */
bool BaseVariable::is_free_variable() 
{
    return p_free_variable;
}

/**
 * @brief Shows if the variable is classified as forced-free.
 * A variable is referred as forced-free if it can be set by the
 * SMT2 reasoning engine although it has been assigned already.
 *
 * @return The stored forced-free information.
 */
bool BaseVariable::is_forced_free() 
{
    return p_force_free;
}

/**
 * @brief Sets a variable to be un-free.
 * The SMT2 reasoning engine can not set values to the variable anymore.
 */
void BaseVariable::unset_free_variable() 
{
    p_free_variable = false;
}

/**
 * @brief Shows first address in bytes for the variable on the Yassi memory.
 * Every variable lives on the Yassi mixed memory model.
 *
 * @return The first address of the variable.
 */
size_t BaseVariable::get_firstaddress() 
{
    return p_firstaddress;
}

/**
 * @brief Shows the last address in bytes for the variable on the Yassi memory.
 * Every variable lives on the Yassi mixed memory model.
 *
 * @return The last address of the variable.
 */
size_t BaseVariable::get_lastaddress() 
{
    return p_lastaddress;
}

/**
 * @brief Set Start Address (Byte) of the Variable in the Memory
 * 
 * @param firstaddress: The Start Address
 */
void BaseVariable::set_firstaddress(size_t const firstaddress) 
{
    p_firstaddress = firstaddress;
}

/**
 * @brief Set Last Address (Byte) of the Variable in the Memory
 * 
 * @param lastaddress: The Last Address
 */
void BaseVariable::set_lastaddress(size_t const lastaddress) 
{
    p_lastaddress = lastaddress;
}

/**
 * @brief Get Value as String
 * 
 * @return std::string
 */
std::string BaseVariable::get_value_as_string(){
    if(p_value == "true" || p_value == "True"){
        return "1";
    } else if (p_value == "false" || p_value == "False"){
        return "0";
    } else if (p_value == "X"){
        return "X";
    } else if (p_value.empty()){
        return "0";
    } else {
        return p_value;
    }
}

/**
 * @brief Get Value as Signed 16 Bit Integer
 * 
 * @return int16_t
 */
int16_t BaseVariable::get_value_i16() 
{
    return static_cast<int16_t>(std::stoi(this->get_value_as_string()));
}

/**
 * @brief Get Value as Signed 32 Bit Integer
 * 
 * @return int32_t
 */
int32_t BaseVariable::get_value_i32() 
{
    try {
        std::string value = this->get_value_as_string();
        return static_cast<int32_t>(std::stoi(value));
    
    } catch(z3::exception const & exp){
        throw YassiException(exp.msg());
    }
}

/**
 * @brief Get Value as Signed 64 Bit Integer
 *
 * @return int64_t
 */
int64_t BaseVariable::get_value_i64() 
{
    try {
        return static_cast<int64_t>(std::stol(this->get_value_as_string()));
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Get Value as Signed 8 Bit Integer
 *
 * @return int8_t
 */
int8_t BaseVariable::get_value_i8() 
{
    try {
        std::string value = this->get_value_as_string();
       
        return static_cast<int8_t>(std::stoi(value));
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Get Value as Unsinged 16 Bit Integer
 *
 * @return uint16_t
 */
uint16_t BaseVariable::get_value_ui16() 
{
    try {
        return static_cast<uint16_t>(std::stoi(this->get_value_as_string()));
        
    } catch(std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Get Value as Unsigned 32 Bit Integer
 *
 * @return uint32_t
 */
uint32_t BaseVariable::get_value_ui32() 
{
    try {
        std::string value = this->get_value_as_string();

        unsigned long value_long = std::stol(value);
        uint32_t value_uint32 = static_cast<uint32_t>(value_long);

        return value_uint32;
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Get Value as Unsigned 64 Bit Integer
 *
 * @return uint64_t
 */
uint64_t BaseVariable::get_value_ui64() 
{
    try {
        return static_cast<uint64_t>(std::stol(this->get_value_as_string()));
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Get Value as Unsigned 8 Bit Integer
 *
 * @return uint8_t
 */
uint8_t BaseVariable::get_value_ui8() 
{
    try {
        return static_cast<uint8_t>(std::stoi(this->get_value_as_string()));
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Get Value as Double
 *
 * @return double
 */
double BaseVariable::get_value_double_precision() 
{
    return std::stod(this->get_value_as_string());
}

/**
 * @brief Get Value as Float
 *
 * @return float
 */
float BaseVariable::get_value_single_precision() 
{
    return std::stof(this->get_value_as_string());
}

/**
 * @brief Get Value as Boolean
 *
 * @return bool
 */
bool BaseVariable::get_value_bool() 
{
    std::string val = this->get_value_as_string();
    
    if(val == "1" || val == "true"){
        return true;
    } else if (val == "0" || val == "false"){
        return false;
    } else {
        throw YassiException("Can not translate Boolean Value");
    }
}

/**
 * @brief Get Sign (Positive/Negative) of Value
 *
 * @return Yassi::eSign
 */
eSign BaseVariable::get_sign()
{
    return p_sign;
}

/**
 * @brief Set Sign (Positive/Negative) of Value
 * 
 * @param sign
 */
void BaseVariable::set_sign(eSign const sign)
{
    p_sign = sign;
}

/**
 * @brief Get Type of Variable
 * 
 * @return Yassi::BaseType*
 */
BaseType* BaseVariable::get_type() 
{
    nullpointer_check(p_type);
    
    return p_type;
}

/**
 * @brief Set Type of Variable
 * 
 * @param next_type Type Object
 */
void BaseVariable::set_type(BaseType* next_type) 
{
    nullpointer_check(next_type);
    
    throw YassiException("Update SMT Instance!");
    p_type = next_type;
}

/**
 * @brief Check if Variable if Propagated
 * 
 * @return bool
 */
bool BaseVariable::is_propaged_constant()
{
    return propageted_constant;
}

/**
 * @brief Set Variable is Propagated
 */
void BaseVariable::set_propagated_constant()
{
    propageted_constant = true;
}

/**
 * @brief Get Origin Variable of Variable
 * 
 * @return Yassi::BaseVariable*
 */
BaseVariable* BaseVariable::get_propagated_from()
{
    return p_propagated_from;
}

/**
 * @brief Set Propagated From 
 * 
 * @param var Origin Variable
 */
void BaseVariable::set_propagated_from(BaseVariable* var)
{
    assert (var != nullptr);
    nullpointer_check(var);
    
    if(var != this){
        propageted_constant = true;
        p_propagated_from = var;
    }
}

/**
 * @brief Set Value of the Variable
 * 
 * @param next_value: The new value
 */
void BaseVariable::set_value(std::string next_value) 
{
    if(p_force_free == false || !BaseUtils::is_uninitialized_value(next_value)){
        this->unset_free_variable();
    }
    p_value = next_value;
}

/**
 * @brief  Set the value of a free variable
 * 
 * @param next_value:
 */
void BaseVariable::set_value_free_variable(std::string const & next_value)
{
    p_value = next_value;
}

/**
 * @brief Set new SMT Formula holding
 * 
 * @param new_formula: The new SMT Formula
 */
void BaseVariable::set_smt_formula(z3::expr new_formula)
{
    p_smt_formula = new_formula;
    p_obsolete_smt_formula = false;
}

/**
 * @brief Reset the SMT Instance of the Variable
 */
void BaseVariable::clear_smt_formula()
{
    p_smt_formula = p_smt_formula = p_z3_ctx->string_val("INIT");
    p_obsolete_smt_formula = true;
}

/**
 * @brief Get Index Assertion for Dereferencing
 * 
 * @return z3::expr
 */
z3::expr BaseVariable::get_index_assertion()
{
    return p_index_assertion;
}

/**
 * @brief Set Index Assertion for Dereferencing
 * 
 * @param assertion:
 */
void BaseVariable::set_index_assertion(z3::expr assertion)
{
    p_index_assertion = assertion;
    p_has_index_assertion = true;
}

/**
 * @brief Check if Variable has Index Assertion
 * 
 * @return bool
 */
bool BaseVariable::has_index_assertion()
{
    return p_has_index_assertion;
}

/**
 * @brief Set Variable Forced Free to be Included into the SMT Instance
 */
void BaseVariable::set_force_free()
{
    p_force_free = true;
    p_constant = false;
    p_obsolete_smt_formula = true;
}

/**
 * @brief Check if Variable is part of the SMT Solution
 * 
 * @return bool
 */
bool BaseVariable::used()
{
    return p_obsolete_smt_formula == false;
}

/**
 * @brief Check if Variable if Constant
 * 
 * @return bool
 */
bool BaseVariable::is_constant()
{
    return p_constant;
}

/**
 * @brief Check if Variable is Return Value from External Function
 * 
 * @return bool
 */
bool BaseVariable::get_comes_from_nonannotated()
{
    return p_comes_from_nonannotated;
}

/**
 * @brief Set Variable is Return Value from External Function
 *
 * @param val:
 */
void BaseVariable::set_comes_from_nonannoated(bool const val)
{
    p_comes_from_nonannotated = val;
}

/**
 * @brief Check if Variable is Linear Dependent to Constants
 * 
 * @return bool
 */
bool BaseVariable::get_is_linear()
{
    return p_linear && !p_force_free;
}

/**
 * @brief Set Linear Dependency of Variable
 * 
 * @param val
 */
void BaseVariable::set_is_linear(bool const val)
{
    p_linear = val;
}

/**
 * @brief Get Memory Position the Variable has been Allocated
 * 
 * @return size_t
 */
size_t BaseVariable::get_alloc_point()
{
    return p_alloc_point;
}

/**
 * @brief Set Memory Position the Variable has been Allocated
 * 
 * @param val The Memory Position
 */
void BaseVariable::set_alloc_point(size_t const val)
{
    p_alloc_point = val;
}

/**
 * @brief Check if Variable is Function Pointer
 * 
 * @return bool
 */
bool BaseVariable::is_function_pointer()
{
    return p_function_pointer;
}

/**
 * @brief Set Function Poiner
 * 
 * @param fp: Valeu
 */
void BaseVariable::set_funtion_pointer(bool const fp)
{
    p_function_pointer = fp;
}

/**
 * @brief Insert the possible Indexes for Array Dereferencing
 * 
 * @param val: Indexes
 */
void BaseVariable::insert_index(std::vector<size_t> const & val)
{
    p_index_values.push_back(val);
}

/**
 * @brief Get the possible Indexes for Array Dereferencing
 * 
 * @return std::vector< size_t >
 */
std::vector<std::vector<size_t>> BaseVariable::get_index_values()
{
    return p_index_values;
}

/**
 * @brief Delete all Indexes 
 */
void BaseVariable::clear_indexes()
{
    p_index_values.clear();
}

/**
 * @brief Check if Variable holds Indexes
 * 
 * @return bool
 */
bool BaseVariable::has_indexes()
{
    return p_index_values.size();
}

/**
 * @brief Get Index Base Pointer (First Element of Array)
 * 
 * @return Yassi::BaseVariable*
 */
std::vector<BaseVariable*> BaseVariable::get_index_base_pointer()
{
    return p_index_base_pointer;
}

/**
 * @brief 
 * 
 * @param ptr:
 */
void BaseVariable::add_index_base_pointer(BaseVariable* ptr)
{
    nullpointer_check(ptr);
    p_index_base_pointer.push_back(ptr);
}

void BaseVariable::clear_index_base_pointer()
{
    p_index_base_pointer.clear();
}

/**
 * @brief
 * 
 * @return Yassi::BaseVariable*
 */
BaseVariable * BaseVariable::get_parent()
{
    return p_parent;
}

/**
 * @brief
 * 
 * @param ptr:
 */
void BaseVariable::set_parent(BaseVariable* ptr)
{
    p_parent = ptr;
}

/**
 * @brief
 */
void BaseVariable::unset_constant()
{
    p_constant = false;
}

/**
 * @brief
 */
void BaseVariable::set_constant()
{
    p_constant = true;
}

/**
 * @brief
 * 
 * @return Yassi::BaseVariable*
 */
std::vector<BaseVariable*> BaseVariable::get_index_var()
{
    return p_index_variable;
}

/**
 * @brief
 *
 * @param var:
 */
void BaseVariable::add_index_var(BaseVariable* var)
{
    p_index_variable.push_back(var);
}

void BaseVariable::clear_index_var()
{
    p_index_variable.clear();
}

/**
 * @brief
 * 
 * @return std::string
 */
std::string BaseVariable::get_function()
{
    return p_function;
}

/**
 * @brief
 * 
 * @param function:
 */
void BaseVariable::set_function(std::string const & function)
{
    p_function = function;
}

/**
 * @brief
 * 
 * @return std::string
 */
std::string BaseVariable::get_sourcefile()
{
    return p_source_file;
}

/**
 * @brief
 * 
 * @param sourcefile:
 */
void BaseVariable::set_sourcefile(std::string const& sourcefile)
{
    p_source_file = sourcefile;
}

/**
 * @brief
 * 
 * @return Yassi::eAllocationType
 */
eAllocationType BaseVariable::get_allocation_type()
{
    return p_allocation_type;
}

/**
 * @brief
 * 
 * @param alloc_type:
 */
void BaseVariable::set_allocation_type(eAllocationType const alloc_type)
{
    p_allocation_type = alloc_type;
}

/**
 * @brief ...
 * 
 * @return bool
 */
bool BaseVariable::is_global()
{
    return p_global;
}

/**
 * @brief ...
 */
void BaseVariable::set_global()
{
    p_global = true;
}

/**
 * @brief ...
 * 
 * @param alignment
 */
void BaseVariable::set_index_alignment(std::vector<std::pair<size_t,
                                       size_t>> const & alignment)
{
    p_index_alignment = alignment;
}

/**
 * @brief ...
 * 
 * @return std::vector< std::pair< size_t, size_t > >
 */
std::vector<std::pair<size_t, size_t> > BaseVariable::get_index_alignment()
{
    return p_index_alignment;
}

/**
 * @brief ...
 * 
 * @return std::string
 */
std::string BaseVariable::get_offset_tree()
{
    return p_offset_tree;
}

/**
 * @brief ...
 * 
 * @param offset_tree p_offset_tree:...
 */
void BaseVariable::set_offset_tree(std::string const & offset_tree)
{
    p_offset_tree = offset_tree;
}

/**
 * @brief ...
 * 
 * @return bool
 */
bool BaseVariable::has_offset_tree()
{
    return !p_offset_tree.empty();
}
