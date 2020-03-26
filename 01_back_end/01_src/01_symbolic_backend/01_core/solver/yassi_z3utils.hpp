/** 
 * @file yassi_z3utils.hpp
 * @brief Utility Classes for Z3
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
#ifndef YASSI_Z3UTILS_HPP
#define YASSI_Z3UTILS_HPP

#include <z3++.h>
#include <z3.h>

namespace Yassi::Backend::Execute {

/**
 * @class Z3Utils
 * @brief Utility Functions for Z3
 */
class Z3Utils {
public:
    static z3::expr mk_add_bv(z3::expr_vector const & expr);

    static std::string get_solver_version();
};

}

#endif /* YASSI_Z3UTILS_HPP */
