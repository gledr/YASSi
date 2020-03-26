/** 
 * @file yassi_replay.cpp
 * @brief Typesafe Access Point Class for the Replay Execution
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
#include "yassi_replay.hpp"

using namespace Yassi::Backend::Replay;


/**
 * @brief Constructor
 */
Replay::Replay():
    Object()
{
    this->options_from_db();
    
    p_observer = new ObserveModel();
    p_stimuli = new StimulateModel();
}

/**
 * @brief Destructor
 */
Replay::~Replay() 
{
    delete p_observer; p_observer = nullptr;
    delete p_stimuli; p_stimuli = nullptr;
}

/**
 * @brief Insert Found Trace into Database
 */
void Replay::next_trace() 
{
    p_observer->next_trace();
}

/**
 * @brief Entering BasisBlock
 * 
 * @param _bb Name of the BasicBlock
 */
void Replay::begin_bb(char* _bb) 
{
    nullpointer_check(_bb);
    
    p_observer->begin_bb(_bb);
}

/**
 * @brief Leaving BasicBlock
 * 
 * @param _bb Name of the BasicBlock
 */
void Replay::end_bb(char* _bb) 
{
    nullpointer_check(_bb);
    
    p_observer->end_bb(_bb);
}

/** 
 * @brief Entering Called Function
 * 
 * @param _fn_name Name of the Function
 * @param _oplist Arguments of the Function
 * @param _source_file Source File containing the Function
 */
void Replay::begin_fn(char* _fn_name, char* _oplist, char* _source_file) 
{
    nullpointer_check(_fn_name);
    nullpointer_check(_oplist);
    nullpointer_check(_source_file);
    
    (void) _oplist; // Make Compiler Happy :) 

    p_observer->begin_fn(_fn_name, _source_file);
}

/**
 * @brief Leaving Function
 */
void Replay::end_fn() 
{
    p_observer->end_fn();
}

/**
 * @brief Begin Simulation
 */
void Replay::begin_sim() 
{
    p_stimuli->begin_sim();
    p_observer->begin_sim();
}

/**
 * @brief Terminating Simulation
 */
void Replay::end_sim() 
{
    p_stimuli->end_sim();
    p_observer->end_sim();
}

/**
 * @brief Conditional Branch Rached
 * 
 * @param value Take of Reject Branch
 */
void Replay::br_instr_cond(bool value) 
{
    p_observer->br_instr_cond(value);
}

/**
 * @brief
 * 
 * @param _name
 * @return char
 */
char Replay::vector_char(char* _name) 
{
    nullpointer_check(_name);

    return p_stimuli->vector_char(_name);
}

/**
 * @brief
 * 
 * @param _name
 * @return float
 */
float Replay::vector_float(char* _name) 
{
    nullpointer_check(_name);
    
    return p_stimuli->vector_float(_name);
}

/**
 * @brief 
 * 
 * @param _name
 * @return double
 */
double Replay::vector_double(char* _name) 
{
    nullpointer_check(_name);
    
    return p_stimuli->vector_double(_name);
}

/**
 * @brief
 * 
 * @param _name
 * @return int
 */
int Replay::vector_int(char* _name) 
{
    nullpointer_check(_name);
    
    return p_stimuli->vector_int(_name);;
}

/**
 * @brief
 * 
 * @param _name
 * @return long int
 */
long Replay::vector_long(char* _name) 
{
    nullpointer_check(_name);
    
    return p_stimuli->vector_long(_name);
}

/**
 * @brief
 * 
 * @param _name
 * @return short int
 */
short Replay::vector_short(char* _name)
{
    nullpointer_check(_name);
    
    return p_stimuli->vector_short(_name);
}

/**
 * @brief
 * 
 * @param val
 */
void Replay::__VERIFIER_assert(int val)
{
    p_observer->__VERIFIER_assert(val);
}

/**
 * @brief
 * 
 * @param _assumption
 */
void Replay::__VERIFIER_assume(int _assumption)
{
    p_observer->__VERIFIER_assume(_assumption);
}

/**
 * @brief Load Options Stored into the Database
 */
void Replay::options_from_db()
{
    std::map<std::string, std::string> settings = p_database->get_options();
    this->set_debug(settings["verbose"] == "true" ? true : false);
    this->set_bin_name(settings["replay_backend"]);
    this->set_log_file_enabled(settings["log_file_enabled"] == "true" ? true : false);
    this->set_execution_url(settings["execution_url"]);
}
