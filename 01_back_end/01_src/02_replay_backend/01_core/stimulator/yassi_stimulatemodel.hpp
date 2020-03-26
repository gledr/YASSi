/** 
 * @file yassi_stimulatemodel.hpp
 * @brief Trigger the Execution of the Replay Model using Test Vectors
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
#ifndef YASSI_STIMULATEMODEL_HPP
#define YASSI_STIMULATEMODEL_HPP

#include <string>
#include <vector>
#include <map>
#include <iostream>
#include <memory>
#include <set>
#include <limits>

#include <yassi_object.hpp>
#include <yassi_logger.hpp>

namespace Yassi::Backend::Replay {

/**
 * @class StimulateModel
 * @brief Trigger the Execution of the Replay Model
 */
class StimulateModel: public virtual Object {
public:
    StimulateModel();

    ~StimulateModel();

    void begin_sim();

    void end_sim();

    short vector_short(std::string const & name);

    long vector_long(std::string const & name);

    int vector_int(std::string const & name);

    float vector_float(std::string const & name);

    double vector_double(std::string const & name);

    char vector_char(std::string const & name);

private:
    void load_test_vectors();
    std::map<std::string, std::vector<std::string>> p_test_vectors;

    Logger* p_logger;
};

}

#endif /* YASSI_STIMULATEMODEL_HPP */
