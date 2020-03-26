/** 
 * @file yassi_observemodel.hpp
 * @brief Observe the Execution of the Replay Model
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
#ifndef YASSI_OBSERVEMODEL_HPP
#define YASSI_OBSERVEMODEL_HPP

#include <string>
#include <iostream>
#include <vector>
#include <set>
#include <map>

#include <yassi_object.hpp>
#include <yassi_baseutils.hpp>
#include <yassi_logger.hpp>

namespace Yassi::Backend::Replay {

/**
 * @class ObserveModel
 * @brief Observe the Execution of the Replay Model
 */
class ObserveModel: public virtual Object {
public:
    ObserveModel();

    ~ObserveModel();

    void next_trace();

    void begin_sim();

    void end_sim();

    void begin_bb(std::string const & bb);

    void end_bb(std::string const & bb);

    void begin_fn(std::string const & _fn_name, std::string const & _source_file);

    void end_fn();

    void br_instr_cond(bool value);
    
    void __VERIFIER_assert(int val);
    
    void __VERIFIER_assume(int assumption);

private:
    Logger* p_logger;
    
    std::set<std::pair<std::string, std::string> > p_availible_functions;
    std::set<std::pair<std::string, std::string> > p_visited_functions;
    
    std::set<std::tuple<std::string, std::string, std::string>> p_availible_basicblocks;
    std::set<std::tuple<std::string, std::string, std::string>> p_visited_basicblocks;
   
    std::string p_actual_fn_name;
    std::string p_actual_source_file;
    std::vector<std::string> fn_stack;

    std::list<bool> p_path_stack;
    std::vector<std::string> p_execution_trace;
    
    void show_statistic();
    void get_bb_info_from_db();
};

}

#endif /* YASSI_OBSERVEMODEL_HPP */
