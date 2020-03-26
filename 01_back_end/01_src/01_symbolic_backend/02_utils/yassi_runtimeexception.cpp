/** 
 * @file yassi_runtimeexception.cpp
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
#include "yassi_runtimeexception.hpp"

using namespace Yassi::Backend::Execute;


/**
 * @brief Constructor
 */
RunTimeException::RunTimeException():
    Object()
{
    p_logger = Logger::getInstance();
    p_memory = Memory::getInstance();
    p_database = new Database(this->get_database_url());
}

/**
 * @brief Destructor
 */
RunTimeException::~RunTimeException()
{
    delete p_database; p_database = nullptr;
    p_logger = nullptr;
    p_memory = nullptr;
}

/**
 * @brief Terminate Execution after found Exception
 * 
 * @param what Type of found exception
 * @param description Exception Description
 */
void RunTimeException::trigger_exception(eException const what,
                                         std::string const & description)
{
    p_logger->exception_found(what,
                    this->get_file_being_executed(),
                    std::to_string(this->get_line_num_execution()),
                    description);

    if(what != e_assertion_pass){
        p_database->insert_exception(what,
                    this->get_file_being_executed(),
                    std::to_string(this->get_line_num_execution()));

        p_database->insert_error_trace(this->get_path_history());

        std::stringstream query;
        int id = p_database->get_problem_num();
        for(auto& it : p_memory->get_free_variables()){
            if(it->used()){
                query.str("");
                std::string name  = it->get_name();
                std::string hint;
                if(it->get_parent() != nullptr){
                    hint  = it->get_parent()->get_name_hint();
                } else {
                    hint  = it->get_name_hint();
                }
                std::string value = it->get_value_as_string();
                p_database->insert_result(name,
                                          value,
                                          hint,
                                          std::to_string(id));
            }
        }

        p_logger->terminate_backend();
        kill(0, SIGKILL);
    }
}
