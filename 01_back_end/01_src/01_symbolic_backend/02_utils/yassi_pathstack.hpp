/** 
 * @file yassi_pathstack.hpp
 * @brief Path Stack for Execution History
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
 */
#ifndef YASSI_PATHSTACK_HPP
#define YASSI_PATHSTACK_HPP

#include <vector>
#include <string>
#include <sstream>

namespace Yassi::Backend::Execute {

/**
 * @class PathStack
 * @brief Path Stack for Execution History
 */
class PathStack {
public:

    PathStack();

    virtual ~PathStack();

    void push(bool const & val);

    bool top();

    bool pop();

    std::string to_string();

private:
    std::vector<bool> p_stack;
};

}

#endif /* YASSI_PATHSTACK_HPP */
