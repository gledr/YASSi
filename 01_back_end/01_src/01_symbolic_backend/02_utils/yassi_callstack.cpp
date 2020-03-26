/** 
 * @file yassi_callstack.cpp
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
#include "yassi_callstack.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
Callstack::Callstack()
{
    p_logger = Logger::getInstance();
}

/**
 * @brief Destructor
 */
Callstack::~Callstack() 
{
    p_logger = nullptr;
}

/**
 * @brief Pop Element from Stack
 * 
 * @return Yassi::Backend::Execute::CallStackElement
 */
CallStackElement Callstack::pop()
{
    if(!p_callstack.empty()) {
        CallStackElement tmp = p_callstack.back();
        p_callstack.pop_back();
        return tmp;
    } else {
        throw YassiException("Can not pop from empty stack!");
    }
}

/**
 * @brief Print Callstack using Logger
 */
void Callstack::print_callstack()
{
    std::stringstream msg;
    msg << "Callstack: ";
    for(auto it : p_callstack){
        msg <<  it.function_name << " ";
    }

   p_logger->print_callstack(msg.str());
}

/**
 * @brief Push Element to Stack
 * 
 * @param return_to Function called from
 * @param function_name Function to Call
 * @param source_file Source File Containing  Function
 */
void Callstack::push(std::string const & return_to, std::string const & function_name, std::string const & source_file)
{
    CallStackElement tmp;
    tmp.return_to = return_to;
    tmp.function_name = function_name;
    tmp.source_file = source_file;
    p_callstack.push_back(tmp);
}

/**
 * @brief Get top element of Stack
 * 
 * @return Yassi::Backend::Execute::CallStackElement
 */
CallStackElement Callstack::top()
{
    return p_callstack.back();
}

/**
 * @brief Check if Stack is empty
 * 
 * @return bool
 */
bool Callstack::empty()
{
    return p_callstack.empty();
}

/**
 * @brief Get Number of Element in the Stack
 * 
 * @return size_t
 */
size_t Callstack::size()
{
    return p_callstack.size();
}
