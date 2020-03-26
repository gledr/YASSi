/** 
 * @file yassi_typefactory.hpp
 * @brief Factory Class for Types
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
 * 51 
 */
#ifndef YASSI_TYPEFACTORY_HPP
#define YASSI_TYPEFACTORY_HPP

#include <memory>
#include <iostream>

#include "yassi_basetype.hpp"
#include "yassi_booltype.hpp"
#include "yassi_integer1type.hpp"
#include "yassi_integer8type.hpp"
#include "yassi_integer16type.hpp"
#include "yassi_integer32type.hpp"
#include "yassi_integer64type.hpp"
#include "yassi_pointertype.hpp"
#include "yassi_floattype.hpp"
#include "yassi_doubletype.hpp"
#include "yassi_structtype.hpp"
#include "yassi_arraytype.hpp"
#include "yassi_voidtype.hpp"
#include "yassi_functiontype.hpp"

namespace Yassi::Types {

/**
 * @class TypeFactory
 * @brief Factory holding Single Instances for each Type
 * 
 * TypeFactory is the only class allowed to instance Types.
 * TypeFactory is a friend class for all types.
 */
class TypeFactory {
public:
    TypeFactory();

    virtual ~TypeFactory();

    BoolType* get_booltype();

    Integer1Type* get_int1type();

    Integer8Type* get_int8type();

    Integer16Type* get_int16type();

    Integer32Type* get_int32type();

    Integer64Type* get_int64type();

    PointerType* get_pointertype();

    FloatType* get_floattype();

    DoubleType* get_doubletype();

    StructType* get_structtype();

    ArrayType* get_arraytype();

    VoidType* get_voidtype();

    FunctionType* get_functiontype();

    BaseType* get_type_by_identifier(std::string const & identifier);

    BaseType* get_type_by_enum(TypeID const & id, size_t const bit_width = 0);

private:
    BoolType        * p_booltype;
    Integer1Type    * p_int1type;
    Integer8Type    * p_int8type;
    Integer16Type   * p_int16type;
    Integer32Type   * p_int32type;
    Integer64Type   * p_int64type;
    PointerType     * p_pointertype;
    FloatType       * p_floattype;
    DoubleType      * p_doubletype;
    StructType      * p_structtype;
    ArrayType       * p_arraytype;
    VoidType        * p_voidtype;
    FunctionType    * p_functiontype;
};

}

#endif /* YASSI_TYPEFACTORY_HPP */
