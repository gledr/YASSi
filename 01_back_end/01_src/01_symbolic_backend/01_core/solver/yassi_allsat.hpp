/** 
 * @file yassi_allsat.hpp
 * @brief This class realizes AllSAT for Pointer Instructions
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
#ifndef YASSI_ALLSAT_HPP
#define YASSI_ALLSAT_HPP

#include <fstream>

#include <yassi_object.hpp>
#include <yassi_variables.hpp>
#include <yassi_exception.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class AllSAT
 * @brief Realizes AllSAT for Poitner Instructions
 */
class AllSAT: public virtual Object{
public:

    AllSAT(z3::context* z3_ctx);

    virtual ~AllSAT();

    void set_smt_instance(Variables::BaseVariable* expr);

    void run();

    std::vector<size_t> get_results();

private:
    Variables::BaseVariable* p_expr;
    std::vector<size_t> p_allsat_values;
    std::string p_allsat_var;

    z3::solver* p_solver;
    z3::context* p_z3_ctx;

    void dump_to_filesystem();
};

}

#endif /* YASSI_ALLSAT_HPP */
