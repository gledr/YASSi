/** 
 * @file yassi_pointerinstruction.hpp
 * @brief This class realizes operations on Pointer
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
#ifndef YASSI_POINTERINSTRUCTION_HPP
#define YASSI_POINTERINSTRUCTION_HPP

#include <yassi_object.hpp>
#include <yassi_memory.hpp>
#include <yassi_logger.hpp>
#include <yassi_allsat.hpp>
#include <yassi_datastructuretree.hpp>
#include <yassi_variablefactory.hpp>
#include <yassi_runtimeexception.hpp>
#include <yassi_exception.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class PointerInstruction
 * @brief This class realizes operations on Pointer
 */ 
class PointerInstruction: public virtual Object {
public:

    PointerInstruction(z3::context* z3_ctx);
    
    virtual ~PointerInstruction();

    void getelementptr(Variables::BaseVariable* dst,
                       Variables::BaseVariable* pointer,
                       std::vector<Variables::BaseVariable*> & indexes,
                       std::string const & _offset_tree);
    
    void symbolic_load(Variables::BaseVariable* dst,
                       Variables::BaseVariable* addr);

    void symbolic_store(Variables::BaseVariable* src,
                        Variables::BaseVariable* addr);

    void* function_pointer_hook(Variables::BaseVariable* fp_var);

private:

    PointerInstruction (PointerInstruction const & other);
    PointerInstruction& operator= ( PointerInstruction const & other);
    bool operator== ( const PointerInstruction& other ) const;
    bool operator!= ( const PointerInstruction& other ) const;

    bool is_constant_getelementptr(std::vector<Variables::BaseVariable*> var);

    void constant_gep(Variables::BaseVariable* dst,
                      Variables::BaseVariable* pointer,
                      std::vector<Variables::BaseVariable*> & indexes,
                      const std::string& _offset_tree);
    void non_constant_gep(Variables::BaseVariable* dst_var,
                          Variables::BaseVariable* pointer_var,
                          std::vector<Variables::BaseVariable*> & indexes,
                          const std::string& _offset_tree);

    void check_constant_gep(Variables::BaseVariable* dst,
                            Variables::BaseVariable* pointer,
                            std::vector<Variables::BaseVariable*> const & indexes,
                            const std::string& _offset_tree);
    void check_non_constant_gep(Variables::BaseVariable* dst_var,
                                Variables::BaseVariable* pointer_var,
                                std::vector<Variables::BaseVariable*> const & indexes,
                                const std::string& _offset_tree);

    void symbolic_load_1d(Variables::BaseVariable* dst, Variables::BaseVariable* addr);
    void symbolic_load_2d(Variables::BaseVariable* dst, Variables::BaseVariable* addr);

    void symbolic_load_2d_free_const(Variables::BaseVariable* dst, Variables::BaseVariable* addr);
    void symbolic_load_2d_free_free(Variables::BaseVariable* dst, Variables::BaseVariable* addr);

    bool is_symbolic_load_1d(Variables::BaseVariable* addr);
    bool is_symbolic_load_2d(Variables::BaseVariable* addr);

    void clean_up_symbolic_load(Variables::BaseVariable* addr);

    Memory* p_memory;
    Logger* p_logger;
    AllSAT* p_allsat;
    Database* p_database;
    RunTimeException* p_run_time_exception;
    Variables::VariableFactory* p_var_factory;
    Yassi::Utils::DatastructureTree* p_type_tree;

    z3::context* p_z3_ctx;
};

}

#endif /* YASSI_POINTERINSTRUCTION_HPP */
