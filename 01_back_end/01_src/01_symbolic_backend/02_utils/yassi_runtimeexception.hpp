/** 
 * @file yassi_runtimeexception.hpp
 * @brief Class used to handle found Run-Time-Exceptions
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
#ifndef YASSI_RUNTIMEEXCEPTION_HPP
#define YASSI_RUNTIMEEXCEPTION_HPP

#include <yassi_object.hpp>
#include <yassi_database.hpp>
#include <yassi_logger.hpp>
#include <yassi_memory.hpp>

#include <sstream>

namespace Yassi::Backend::Execute {

/**
 * @class RunTimeException
 * @brief Handle found Run-Time-Exceptions
 */
class RunTimeException: public virtual Object {
public:
    RunTimeException();
    virtual ~RunTimeException();

    void trigger_exception(eException const what,
                           std::string const & description = "");

private:
    Logger* p_logger;
    Database* p_database;
    Memory* p_memory;
};

}

#endif /* YASSI_RUNTIMEEXCEPTION_HPP */
