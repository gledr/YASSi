/** 
 * @file yassi_typefactory.cpp
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
#include "yassi_typefactory.hpp"

using namespace Yassi::Types;


/**
 * @brief Constructor
 */
TypeFactory::TypeFactory()
{
    p_booltype      = new BoolType();
    p_int1type      = new Integer1Type();
    p_int8type      = new Integer8Type();
    p_int16type     = new Integer16Type();
    p_int32type     = new Integer32Type();
    p_int64type     = new Integer64Type();
    p_pointertype   = new PointerType();
    p_floattype     = new FloatType();
    p_doubletype    = new DoubleType();
    p_structtype    = new StructType();
    p_arraytype     = new ArrayType();
    p_voidtype      = new VoidType();
    p_functiontype  = new FunctionType();
}

/**
 * @brief Destructor
 */
TypeFactory::~TypeFactory()
{
    delete p_booltype;      p_booltype      = nullptr;
    delete p_int1type;      p_int1type      = nullptr;
    delete p_int8type;      p_int8type      = nullptr;
    delete p_int16type;     p_int16type     = nullptr;
    delete p_int32type;     p_int32type     = nullptr;
    delete p_int64type;     p_int64type     = nullptr;
    delete p_pointertype;   p_pointertype   = nullptr;
    delete p_floattype;     p_floattype     = nullptr;
    delete p_doubletype;    p_doubletype    = nullptr;
    delete p_structtype;    p_structtype    = nullptr;
    delete p_arraytype;     p_arraytype     = nullptr;
    delete p_voidtype;      p_voidtype      = nullptr;
    delete p_functiontype;  p_functiontype  = nullptr;
}

/**
 * @brief Get Pointer to Integer1Type
 * 
 * @return Yassi::Types::Integer1Type*
 */
Integer1Type* TypeFactory::get_int1type() 
{
    nullpointer_check(this->p_int1type);
    return p_int1type;
}

/**
 * @brief Get Pointer to Integer8Type
 *
 * @return Yassi::Types::Integer8Type*
 */
Integer8Type* TypeFactory::get_int8type()
{
    nullpointer_check(this->p_int8type);
    return p_int8type;
}

/**
 * @brief Get Pointer to Integer16Type
 *
 * @return Yassi::Types::Integer16Type*
 */
Integer16Type* TypeFactory::get_int16type() 
{
    nullpointer_check(this->p_int16type);
    return p_int16type;
}

/**
 * @brief Get Pointer to Integer32Type
 *
 * @return Yassi::Types::Integer32Type*
 */
Integer32Type* TypeFactory::get_int32type() 
{
    nullpointer_check(this->p_int32type);
    return p_int32type;
}

/**
 * @brief Get Pointer to Integer64Type
 * 
 * @return Yassi::Types::Integer64Type*
 */
Integer64Type* TypeFactory::get_int64type() 
{
    nullpointer_check(this->p_int64type);
    return p_int64type;
}

/**
 * @brief Get Pointer to BoolType
 * 
 * @return Yassi::Types::BoolType*
 */
BoolType* TypeFactory::get_booltype()
{
    nullpointer_check(this->p_booltype);
    return p_booltype;
}

/**
 * @brief Get Pointer to PointerType
 * 
 * @return Yassi::Types::PointerType*
 */
PointerType* TypeFactory::get_pointertype()
{
    nullpointer_check(this->p_pointertype);
    return p_pointertype;
}

/**
 * @brief Get Pointer to FloatType
 * 
 * @return Yassi::Types::FloatType*
 */
FloatType* TypeFactory::get_floattype()
{
    nullpointer_check(this->p_floattype);
    return p_floattype;
}

/**
 * @brief Get Pointer to DoubleType
 * 
 * @return Yassi::Types::DoubleType*
 */
DoubleType* TypeFactory::get_doubletype()
{
    nullpointer_check(this->p_doubletype);
    return p_doubletype;
}

/**
 * @brief Get Pointer to StructType
 * 
 * @return Yassi::Types::StructType*
 */
StructType* TypeFactory::get_structtype()
{
    nullpointer_check(this->p_structtype);
    return p_structtype;
}

/**
 * @brief Get Pointer to ArrayType
 * 
 * @return Yassi::Types::ArrayType*
 */
ArrayType* TypeFactory::get_arraytype()
{
    nullpointer_check(this->p_arraytype);
    return p_arraytype;
}

/**
 * @brief Get Pointer to VoidType
 * 
 * @return Yassi::Types::VoidType*
 */
VoidType* TypeFactory::get_voidtype()
{
    nullpointer_check(this->p_voidtype);
    return p_voidtype;
}

/**
 * @brief Get Pointer to FunctionType
 * 
 * @return Yassi::Types::FunctionType*
 */
FunctionType* TypeFactory::get_functiontype()
{
    nullpointer_check(this->p_functiontype);
    return p_functiontype;
}

/**
 * @brief Get Pointer to Type Instance by String Identifier
 * 
 * @param identifier String Identifier of the Target Type
 * @return Yassi::Types::BaseType*
 */
BaseType* TypeFactory::get_type_by_identifier(std::string const & identifier)
{
    if(identifier.compare(INTEGER1TYPE) == 0){
        return this->get_int1type();
    } else if (identifier.compare(INTEGER8TYPE) == 0){
        return this->get_int8type();
    } else if (identifier.compare(INTEGER32TYPE) == 0){
        return this->get_int32type();
    } else if (identifier.compare(INTEGER16TYPE) == 0){
        return this->get_int16type();
    } else if (identifier.compare(INTEGER64TYPE) == 0){
        return this->get_int64type();
    } else if (identifier.compare(POINTERTYPE) == 0){
        return this->get_pointertype();
    } else if (identifier.compare(FLOATTYPE) == 0){
        return this->get_floattype();
    } else if (identifier.compare(DOUBLETYPE) == 0){
        return this->get_doubletype();
    } else if (identifier.compare(BOOLTYPE) == 0){
        return this->get_booltype();
    } else if (identifier.compare(STRUCTTYPE) == 0){
        return this->get_structtype();
    } else if (identifier.compare(ARRAYTYPE) == 0){
        return this->get_arraytype();
    } else if (identifier.compare(VOIDTYPE) == 0){
        return this->get_voidtype();
    } else if (identifier.compare(FUNCTIONTYPE) == 0){
        return this->get_functiontype();
    } else {
        notimplemented_check();
        exit(-1);
    }
}

/**
 * @brief Get Pointer to Type Instance by LLVM TypID Enum
 * 
 * @param id LLVM Type Enum
 * @param bit_width Bit Width of the Type (Integer)
 * @return Yassi::Types::BaseType*
 */
BaseType* TypeFactory::get_type_by_enum(TypeID const & id, size_t const bit_width)
{
    switch(id) {
        case TypeID::ArrayTyID: {
            return this->get_arraytype();
        }
        case TypeID::DoubleTyID: {
            return this->get_doubletype();
        }
        case TypeID::FloatTyID: {
            return this->get_floattype();
        }
        case TypeID::FP128TyID: {
            notimplemented_check();
            break;
        } 
        case TypeID::FunctionTyID: {
            return this->get_functiontype();
        }
        case TypeID::HalfTyID: {
            notimplemented_check();
            break;
        }
        case TypeID::IntegerTyID: {
            if(bit_width == 1){
                return this->get_int1type();
            } else if (bit_width == 8){
                return this->get_int8type();
            } else if (bit_width == 16){
                return this->get_int16type();
            } else if (bit_width == 32){
                return this->get_int32type();
            } else if (bit_width == 64) {
                return this->get_int64type();
            } else {
                notimplemented_check();
                break;
            }
        }
        case TypeID::LabelTyID: {
            notimplemented_check();
            break;
        }
        case TypeID::MetadataTyID: {
            notimplemented_check();
            break;
        }
        case TypeID::PointerTyID: {
            return this->get_pointertype();
        }
        case TypeID::PPC_FP128TyID: {
          notimplemented_check();
          break;
        }
        case TypeID::StructTyID: {
            return this->get_structtype();
        }
        case TypeID::VectorTyID: {
            notimplemented_check();
            break;
        }
        case TypeID::VoidTyID: {
            return this->get_voidtype();
        }
        case TypeID::X86_FP80TyID: {
            notimplemented_check();
            break;
        } 
        case TypeID::X86_MMXTyID: {
            notimplemented_check();
            break;
        }
    }
    exit(-1); // Make Compiler Happy
}
