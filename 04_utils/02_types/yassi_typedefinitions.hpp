/** 
 * @file yassi_typedefinitions.cpp
 * @brief Enumerations and Constatnts used in the Types
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
#ifndef YASSI_TYPE_DEFINITIONS_HPP
#define YASSI_TYPE_DEFINITIONS_HPP

namespace Yassi::Types {

std::string const INTEGER1TYPE  = "IntegerTyID1";
std::string const INTEGER8TYPE  = "IntegerTyID8";
std::string const INTEGER16TYPE = "IntegerTyID16";
std::string const INTEGER32TYPE = "IntegerTyID32";
std::string const INTEGER64TYPE = "IntegerTyID64";
std::string const BOOLTYPE      = "Bool";
std::string const POINTERTYPE   = "PointerTyID";
std::string const FLOATTYPE     = "FloatTyID";
std::string const DOUBLETYPE    = "DoubleTyID";
std::string const STRUCTTYPE    = "StructTyID";
std::string const ARRAYTYPE     = "ArrayTyID";
std::string const VOIDTYPE      = "VoidTyID";
std::string const FUNCTIONTYPE  = "FunctionTyID";

std::string const INTEGERTYPECLASS  = "Int";
std::string const BOOLTYPECLASS     = "Bool";
std::string const POINTERTYPECLASS  = "Pointer";
std::string const REALTYPECLASS     = "Real";
std::string const STRUCTTYPECLASS   = "Struct";
std::string const ARRAYTYPECLASS    = "Array";
std::string const VOIDTYPECLASS     = "Void";
std::string const FUNCTIONTYPECLASS = "Function";

enum TypeID {
    // PrimitiveTypes - make sure LastPrimitiveTyID stays up to date.
    VoidTyID = 0,           ///<  0: type with no size
    HalfTyID = 1,           ///<  1: 16-bit floating point type
    FloatTyID = 2,          ///<  2: 32-bit floating point type
    DoubleTyID = 3,         ///<  3: 64-bit floating point type
    X86_FP80TyID = 4,       ///<  4: 80-bit floating point type (X87)
    FP128TyID = 5,          ///<  5: 128-bit floating point type (112-bit mantissa)
    PPC_FP128TyID = 6,      ///<  6: 128-bit floating point type (two 64-bits, PowerPC)
    LabelTyID = 7,          ///<  7: Labels
    MetadataTyID = 8,       ///<  8: Metadata
    X86_MMXTyID = 9,        ///<  9: MMX vectors (64 bits, X86 specific)

    // Derived types... see DerivedTypes.h file.
    // Make sure FirstDerivedTyID stays up to date!
    IntegerTyID = 11,       ///< 10: Arbitrary bit width integers
    FunctionTyID,           ///< 11: Functions
    StructTyID,             ///< 12: Structures
    ArrayTyID,              ///< 13: Arrays
    PointerTyID,            ///< 14: Pointers
    VectorTyID              ///< 15: SIMD 'packed' format, or other vector type
};

}

#endif /* YASSI_TYPE_DEFINITIONS_HPP */
