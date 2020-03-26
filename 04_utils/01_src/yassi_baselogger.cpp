/** 
 * @file yassi_baselogger.cpp
 * @brief BaseLogger Class for Yassi
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
#include "yassi_baselogger.hpp"

using namespace Yassi::Utils;


LogStream* BaseLogger::p_log_stream = nullptr;

/**
 * @brief Constructor
 */
BaseLogger::BaseLogger()
{
    p_log_stream = new LogStream();
}

/**
 * @brief Destructor
 */
BaseLogger::~BaseLogger()
{
    delete p_log_stream; p_log_stream = nullptr;
}

/**
 * @brief Logging Method
 * 
 * @param level Log Leve to be used.
 * @return Yassi::Utils::LogStream
 */
LogStream BaseLogger::LOG(LogSeverity const & level)
{
    p_log_stream->set_log_level(level);
    return *(BaseLogger::p_log_stream);
}
