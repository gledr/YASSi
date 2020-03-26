/** 
 * @file yassi_basetype.cpp
 * @brief BaseType used for Yassi
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
#include "yassi_basetype.hpp"

using namespace Yassi::Types;


/**
 * @brief Constructor
 */
BaseType::BaseType()
{
}

/**
 * @brief Destructor
 */
BaseType::~BaseType()
{
}

/**
 * @brief Dump Type Information to given stream
 *
 * @param stream: The stream to pipe the Information to
 */
void BaseType::dump(std::ostream& stream)
{
    stream << std::string(10, '#') << std::endl;
    stream << p_type_name << std::endl;
    stream << std::string(10, '#') << std::endl;
}

/**
 * @brief Get the number of bytes allocated by the type
 *
 * @return size_t
 */
size_t BaseType::get_bytes()
{
    if(p_bit_width < 8){
        return 1;
    } else if (p_bit_width % 8 == 0){
        return p_bit_width/8;
    } else {
        return (p_bit_width/8)+1;
    }
}

/**
 * @brief Get the numbr of bits allocated by the type
 *
 * @return size_t
 */
size_t BaseType::get_bits()
{
    return p_bit_width;
}

/**
 * @brief Get the string identifier of the type
 *
 * @return std::string
 */
std::string BaseType::get_type_identifier()
{
    return p_type_name;
}

/**
 * @brief Get the string type class of the the type
 *
 * @return std::string
 */
std::string BaseType::get_type_class()
{
    return p_type_class;
}

/**
 * @brief Check if given type identifier is integer
 *
 * @param identifier The type identifier to check
 * @return bool
 */
bool BaseType::is_int(std::string const & identifier)
{
    return identifier.compare(INTEGER32TYPE) == 0 ||
           identifier.compare(INTEGER64TYPE) == 0 ||
           identifier.compare(INTEGER16TYPE) == 0 ||
           identifier.compare(INTEGER8TYPE)  == 0 ||
           identifier.compare(INTEGER1TYPE)  == 0;
}

/**
 * @brief Check if given type identifier is real
 *
 * @param identifier The type identifier to check
 * @return bool
 */
bool BaseType::is_real(std::string const & identifier)
{
    return identifier.compare(FLOATTYPE) ||
           identifier.compare(DOUBLETYPE);
}

/**
 * @brief Check if type is Integer (1 Bit)
 *
 * @return bool
 */
bool BaseType::is_int1()
{
    return this->p_id == IntegerTyID && this->p_bit_width == 1;
}

/**
 * @brief Check if type is Integer (8 Bit)
 *
 * @return bool
 */
bool BaseType::is_int8()
{
    return this->p_id == IntegerTyID && this->p_bit_width == 8;
}

/**
 * @brief Check if type is Integer (16 Bit)
 *
 * @return bool
 */
bool BaseType::is_int16()
{
    return this->p_id == IntegerTyID && this->p_bit_width == 16;
}

/**
 * @brief Check if type is Integer (32 Bit)
 * 
 * @return bool
 */
bool BaseType::is_int32()
{
    return this->p_id == IntegerTyID && this->p_bit_width == 32;
}

/**
 * @brief Check if type is Integer (64 Bit)
 *
 * @return bool
 */
bool BaseType::is_int64()
{
    return this->p_id == IntegerTyID && this->p_bit_width == 64;
}

/**
 * @brief Check if type is integer class (Int1, Int8, etc, ...)
 *
 * @return bool
 */
bool BaseType::is_integer_class()
{
    return (this->p_id == IntegerTyID) && (this->p_type_class != BOOLTYPECLASS);
}

/**
 * @brief Check if type is integer class (Float, Double)
 *
 * @return bool
 */
bool BaseType::is_real_class()
{
    return this->p_id == DoubleTyID || this->p_id == FloatTyID;
}

/**
 * @brief Check if type if float
 *
 * @return bool
 */
bool BaseType::is_float()
{
    return this->p_id == FloatTyID;
}

/**
 * @brief Check if type is double
 *
 * @return bool
 */
bool BaseType::is_double()
{
    return this->p_id == DoubleTyID;
}

/**
 * @brief Check if type is Boolean class
 *
 * @return bool
 */
bool BaseType::is_bool_class()
{
    return this->get_type_class() == BOOLTYPECLASS;
}

/**
 * @brief Check if type is pointer
 *
 * @return bool
 */
bool BaseType::is_pointer()
{
    return this->get_type_identifier() == POINTERTYPE;
}

/**
 * @brief Check if type is struct
 *
 * @return bool
 */
bool BaseType::is_struct()
{
    return this->p_id == StructTyID;
}

/**
 * @brief Check if type is array
 *
 * @return bool
 */
bool BaseType::is_array()
{
    return this->p_id == ArrayTyID;
}

/**
 * @brief Check if type is void
 *
 * @return bool
 */
bool BaseType::is_void()
{
    return this->p_id == VoidTyID;
}

/**
 * @brief Check if type is function
 *
 * @return bool
 */
bool BaseType::is_function()
{
    return this->p_id == FunctionTyID;
}

/**
 * @brief Compare operator
 *
 * @param type Type to compare with
 * @return bool
 */
bool BaseType::operator==(BaseType* type)
{
    nullpointer_check(type);
    return this->get_type_identifier() == type->get_type_identifier();
}

/**
 * @brief Not equal operator
 * 
 * @param type: The type to compare with
 * @return bool
 */
bool BaseType::operator!=(BaseType* type)
{
    nullpointer_check(type);
    return this->get_type_identifier() != type->get_type_identifier();
}
