/** 
 * @file yassi_replay.hpp
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
#ifndef YASSI_REPLAY_HPP
#define YASSI_REPLAY_HPP

#include <string>

#include <yassi_object.hpp>
#include <yassi_stimulatemodel.hpp>
#include <yassi_observemodel.hpp>
#include <yassi_exception.hpp>

namespace Yassi::Backend::Replay {

class Replay: public virtual Object {
public: 
    Replay();
    
    virtual ~Replay();
    
    void next_trace();
    
    void begin_bb(char* bb);
    
    void end_bb(char* bb);
    
    void begin_fn(char* fn_name, char* oplist, char* source_file);
    
    void end_fn();
    
    void begin_sim();

    void end_sim();
    
    void br_instr_cond(bool value);

    short vector_short(char* _name);

    long vector_long(char* _name);

    int vector_int(char* _name);

    float vector_float(char* _name);
    
    double vector_double(char* _name);

    char vector_char(char* _name);
    
    void __VERIFIER_assert(int val);
    
    void __VERIFIER_assume(int _assumption);
    
private:
    StimulateModel* p_stimuli;
    ObserveModel* p_observer;
    
    void options_from_db();
};

}

#endif /* YASSI_REPLAY_HPP */
