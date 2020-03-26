/** 
 * @file yassi_intrinsics.hpp
 * @brief This class realizes the Instrinsic Functions for Verification
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
#ifndef YASSI_INTRINSICS_HPP
#define YASSI_INTRINSICS_HPP

#include <yassi_object.hpp>
#include <yassi_memory.hpp>
#include <yassi_logger.hpp>
#include <yassi_database.hpp>
#include <yassi_solver.hpp>
#include <yassi_variables.hpp>
#include <yassi_types.hpp>
#include <yassi_typecast.hpp>
#include <yassi_runtimeexception.hpp>
#include <yassi_exception.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class Instrinsic
 * @brief Implemetation of the Verification Instrinsics
 */
class Intrinsics: public virtual Object {
public:

    Intrinsics(z3::context* ctx, z3::solver* slv);
    virtual ~Intrinsics();

    char nondet_char();
    int  nondet_int();
    unsigned int nondet_uint();
    bool nondet_bool();
    long nondet_long();
    void* nondet_pointer();

    void assertion(std::string const & assertion_register);
    void assume(std::string const & assumption_register);

    void error();

private:
    Logger* p_logger;
    Memory* p_memory;
    Database* p_database;
    Variables::VariableFactory* p_var_factory;
    Yassi::Types::TypeFactory* p_type_factory;
    RunTimeException* p_run_time_exception;
    TypeCast* p_type_cast;

    z3::context* p_z3_ctx;
    z3::solver* p_z3_slv;
};

}

#endif /* YASSI_INTRINSICS_HPP */
