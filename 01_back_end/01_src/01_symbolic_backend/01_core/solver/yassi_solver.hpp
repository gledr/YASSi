/** 
 * @file yassi_solver.hpp
 * @brief Solve SMT Problems using the Z3 Library
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
#ifndef YASSI_SOLVER_HPP
#define YASSI_SOLVER_HPP

#include <string>
#include <sstream>

#include <yassi_object.hpp>
#include <yassi_database.hpp>
#include <yassi_memory.hpp>
#include <yassi_fpa.hpp>
#include <yassi_object.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class Solver
 * @brief Solve SMT Problems using the Z3 Library
 */ 
class Solver: public virtual Object {
public:
    Solver(Database* database, z3::context* z3_ctx, z3::solver* z3_slv);

    virtual ~Solver();

    void solve_problem();

    void insert_problem_to_db();

    void insert_variables_to_db();

    void dump_problem_to_directory();

    bool sat();

    std::vector<std::string> get_assertions_smt2();

    std::string get_assertions_smt2_concat();
private:
    Memory* p_memory;
    Database* p_database;
    FloatingPointArithmetic* p_fpa;

    z3::context* p_z3_ctx;
    z3::solver* p_z3_slv;
    z3::check_result p_sat;

    void handle_integer_type(z3::expr & expr, Variables::BaseVariable* var);
    void handle_real_type(z3::expr & expr, Variables::BaseVariable* var);
    void handle_pointer_type(z3::expr & expr, Variables::BaseVariable* var);
};

}

#endif /* YASSI_SOLVER_HPP */
