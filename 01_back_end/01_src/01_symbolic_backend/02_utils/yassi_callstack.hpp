/** 
 * @file yassi_callstack.hpp
 * @brief Call Stack for Execution History
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
#ifndef YASSI_CALLSTACK_HPP
#define YASSI_CALLSTACK_HPP

#include <list>
#include <iostream>

#include <yassi_logger.hpp>
#include <yassi_exception.hpp>

namespace Yassi::Backend::Execute {
    
/**
 * @class CallStackElement
 * @brief CallStackElement holding Information
 */
struct CallStackElement{
    std::string return_to;
    std::string function_name;
    std::string source_file;
};

/**
 * @class CallStack
 * @brief Call Stack for Execution History
 */
class Callstack {
public:
    Callstack();
    
    virtual ~Callstack();

    void push(std::string const & return_to,
              std::string const & function_name,
              std::string const & source_file);

    CallStackElement top();

    CallStackElement pop();

    void print_callstack();

    bool empty();

    size_t size();

private:
    std::list<CallStackElement> p_callstack;
    Logger* p_logger;
};

}
#endif /* YASSI_CALLSTACK_HPP */
