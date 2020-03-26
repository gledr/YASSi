/** 
 * @file yassi_checkmodel.hpp
 * @brief Instrument, Compile and Execute Symbolic Backend Binary
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
#ifndef YASSI_CHECKMODEL_HPP
#define YASSI_CHECKMODEL_HPP

#include <yassi_bitcode.hpp>
#include <yassi_timer.hpp>
#include <yassi_resultchecker.hpp>

#include <json/json.h>
#include <iomanip>
#include <thread>

#include <sys/stat.h>

namespace Yassi::Frontend {

enum eResultsSource {eDatabase, eGoldenResult};

/**
 * @class CheckModel
 * @brief Instrument, Compile and Execute Symbolic Backend Binary
 */
class CheckModel: public Bitcode {
public:
    CheckModel();

    virtual ~CheckModel();

    void instrument_bitcode();

    void link_backend_binary();

    void execute_backend();

    void check_results();

    void compare_bitcode();

    void show_cfg();

    void get_gold_result();

    void show_results(eResultsSource const source);

    void show_exceptions(eResultsSource const source);

    void show_instr_bitcode();

private:
    Timer* p_timer;
    Yassi::Utils::ResultChecker* p_checker;

    void show_execution_traces();

    static void timer_handler(int sig, siginfo_t *si, void *uc);

    static pid_t p_pid;
    static timer_t p_timerid;
};

}

#endif /* YASSI_CHECKMODEL_HPP */
