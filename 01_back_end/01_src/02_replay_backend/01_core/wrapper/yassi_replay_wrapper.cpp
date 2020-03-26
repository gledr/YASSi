/** 
 * @file yassi_replay_wrapper.cpp
 * @brief backend Interface for the Replay Backend
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
 * @author Sebastian Pointner
 * @author Pablo Gonzales de Aledo
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
#include "yassi_replay_wrapper.hpp"
#include "yassi_replay.hpp"

using namespace Yassi::Backend::Replay;


Replay* p_replay = nullptr;

void next_trace() 
{
    p_replay->next_trace();
}

void __REPLAY_begin_bb(char* bb) 
{
    p_replay->begin_bb(bb);
}

void __REPLAY_end_bb(char* bb) 
{
    p_replay->end_bb(bb);
}

void __REPLAY_begin_fn(char* _fn_name, char* _fn_oplist, char* _source_file) 
{
    p_replay->begin_fn(_fn_name, _fn_oplist, _source_file);
}

void __REPLAY_end_fn() 
{
    p_replay->end_fn();
}

void __REPLAY_begin_sim() 
{
    p_replay = new Replay();
    p_replay->begin_sim();
}

void __REPLAY_end_sim() 
{
    p_replay->end_sim();
    delete p_replay; p_replay = nullptr;
}

void __REPLAY_br_instr_cond(bool value) 
{
    p_replay->br_instr_cond(value);
}

short __REPLAY_vector_short(char* _name) 
{
    return p_replay->vector_short(_name);
}

long __REPLAY_vector_long(char* _name) 
{
    return p_replay->vector_long(_name);
}

int __REPLAY_vector_int(char* _name) 
{
    return p_replay->vector_int(_name);
}

float __REPLAY_vector_float(char* _name)
{
    return p_replay->vector_float(_name);
}

double __REPLAY_vector_double(char* _name)
{
    return p_replay->vector_double(_name);
}

char __REPLAY_vector_char(char* _name) 
{
    return p_replay->vector_char(_name);
}

void __VERIFIER_assert(int assertion)
{
    p_replay->__VERIFIER_assert(assertion);
}

void __VERIFIER_assume(int _assumption)
{
    p_replay->__VERIFIER_assume(_assumption);
}
