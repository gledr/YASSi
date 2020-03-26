/** 
 * @file yassi_observemodel.cpp
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
#include "yassi_observemodel.hpp"

using namespace Yassi::Backend::Replay;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
ObserveModel::ObserveModel():
    Object()
{
    p_logger = Logger::getInstance();
}

/**
 * @brief Destructor
 */
ObserveModel::~ObserveModel() 
{
    p_logger = nullptr;
}

/**
 * @brief Begin Replay
 */
void ObserveModel::begin_sim() 
{
    this->get_bb_info_from_db();
    
    for(auto& itor: p_availible_basicblocks){
        p_availible_functions.insert(std::make_pair(std::get<0>(itor), std::get<1>(itor)));
    }
    p_logger->begin_simulation();
}

/**
 * @brief End Replay
 */
void ObserveModel::end_sim() 
{
    p_database->insert_measurement_trace(p_execution_trace);
    this->show_statistic();
    
    std::stringstream value;

    value.str("");
    value << p_visited_functions.size() << "/" << p_availible_functions.size() << " ( " <<
          (int)(100.0*(float)p_visited_functions.size()/(float)p_availible_functions.size()) << " % )";

    p_database->insert_measurement("visited_fns", value.str());

    value.str("");
    value << p_visited_basicblocks.size() << "/" << p_availible_basicblocks.size() << " ( " <<
          (int)(100.0*(float)p_visited_basicblocks.size()/(float)p_availible_basicblocks.size())<< " % )";
    
    p_database->insert_measurement("visited_bbs", value.str());
    p_logger->end_simulation();
}

/**
 * @brief Entering BasicBlock
 * 
 * @param _name Name of the BasicBlock
 */
void ObserveModel::begin_bb(std::string const & _name) 
{
    p_execution_trace.push_back(_name);
    p_database->insert_basic_block(p_actual_source_file, p_actual_fn_name, _name);
    p_visited_basicblocks.insert(std::make_tuple(p_actual_source_file, p_actual_fn_name, _name));
    p_logger->begin_bb(_name);
}

/**
 * @brief Leaving BasicBlock
 * 
 * @param name Name of the BasicBlock
 */
void ObserveModel::end_bb(std::string const & name) 
{
    p_execution_trace.push_back(name);
    p_database->insert_basic_block(p_actual_source_file, p_actual_fn_name, name);
    p_visited_basicblocks.insert(std::make_tuple(p_actual_source_file, p_actual_fn_name, name));
    p_logger->end_bb(name);
}

/**
 * @brief Entering Function
 * 
 * @param _fn_name Name of the Function
 * @param _source_file Source File containing the Function
 */
void ObserveModel::begin_fn(std::string const & _fn_name, std::string const & _source_file)
{
    p_execution_trace.push_back(_fn_name);
    p_actual_source_file = _source_file;
    p_actual_fn_name = _fn_name;
    fn_stack.push_back(_fn_name);
 
    p_visited_functions.insert(std::make_pair(p_actual_source_file,p_actual_fn_name));
    p_logger->begin_fn(_fn_name);
}

/**
 * @brief Leaving Function
 */
void ObserveModel::end_fn()
{
    assertion_check(fn_stack.size());
    
    p_logger->end_fn(fn_stack.back());
    fn_stack.pop_back();
    
    std::string function_name;
    if(fn_stack.size()){
        function_name = fn_stack.back();
    }
    p_actual_fn_name = function_name;
}

/**
 * @brief Conditional Branch Ahead
 * 
 * @param value Take (1) or Reject (0) the Branch
 */
void ObserveModel::br_instr_cond(bool const value) 
{
    p_path_stack.push_back(value);
    std::string path;

    for(auto stack : p_path_stack){
        path += stack?"T":"F";
    }

    std::stringstream query;
    query << "INSERT into reproduced_problems (path) values (" << "'" << path << "');";
    p_database->db_command(query.str());
    
    p_logger->conditional_branch(value);
}

/**
 * @brief Check if Replay violates assertions
 * 
 * @param val Pass (1), Fail (0) 
 */
void ObserveModel::__VERIFIER_assert(int const val)
{
    if(val){
        p_logger->assertion_pass();
    } else {
        p_logger->assertion_fail();
    }
}

/**
 * @brief Execution Assumptions not used yet!
 * 
 * @param assumption TODO
 */
void ObserveModel::__VERIFIER_assume(int const assumption)
{
    (void) assumption;
}

/**
 * @brief Next Replay Iteration - Store found traces
 */
void ObserveModel::next_trace() 
{
    if(!p_execution_trace.empty()) {
        p_database->insert_measurement_trace(p_execution_trace);
    }
    p_execution_trace.clear();
    if(p_path_stack.size()){
        p_path_stack.clear();
    }
}

/**
 * @brief Show Statistics of the Replay
 */
void ObserveModel::show_statistic()
{
    this->get_debug() && std::cout <<"visited fns " << p_visited_functions.size() << " " << p_availible_functions.size() << std::endl;
    this->get_debug() && std::cout <<"visited bbs " << p_visited_basicblocks.size() << " " << p_availible_basicblocks.size() << std::endl;

    this->get_debug() && std::cout << "visited_fns: ";
    for(auto it = p_visited_functions.begin(); it != p_visited_functions.end(); it++ ) {
        this->get_debug() && std::cout << it->first << " " << it->second << std::endl;
    }

    this->get_debug() && std::cout << "available_fns: ";
    for(auto it = p_availible_functions.begin(); it != p_availible_functions.end(); it++ ) {
        this->get_debug() && std::cout << it->first << " " << it->second << std::endl;
    }
  
    this->get_debug() && std::cout << "visited_bbs: ";
    for(auto it : p_visited_basicblocks) {
       this->get_debug() && std::cout << std::get<0>(it) << " " << std::get<1>(it) << " " << std::get<2>(it) << std::endl;
    }

    this->get_debug() && std::cout << "available_bbs: ";
    for(auto& it : p_availible_basicblocks) {
        this->get_debug() && std::cout << std::get<0>(it) << " " << std::get<1>(it) << " " << std::get<2>(it) << std::endl;
    } 
    this->get_debug() && std::cout << std::endl;
}

/**
 * @brief Get possible BasicBlocks from Database
 */
void ObserveModel::get_bb_info_from_db()
{
    p_availible_basicblocks.clear();
    std::vector<BasicBlock> blocks = p_database->get_basic_blocks();
    
    for(auto block: blocks){
        p_availible_basicblocks.insert(std::make_tuple(block.file, block.fn, block.bb));
    }
}
