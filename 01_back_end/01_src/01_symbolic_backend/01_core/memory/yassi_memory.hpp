/** 
 * @file yassi_memory.hpp
 * @brief Yassi Execution Memory
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
#ifndef YASSI_MEMORY_HPP
#define YASSI_MEMORY_HPP

#include <string>
#include <vector>
#include <map>
#include <fstream>

#include <yassi_exception.hpp>
#include <yassi_variables.hpp>
#include <yassi_logger.hpp>
#include <yassi_object.hpp>
#include <yassi_database.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class Memory
 * @brief Yassi's Execution Memory
 */
class Memory: public virtual Object {
public:

    static Memory* getInstance(z3::context* z3_ctx = nullptr);

    static void destroy();

    void alloc_llvm_variable(Variables::BaseVariable* variable);

    void alloc_program_variable(Variables::PointerVariable* obj_ptr,
                                Variables::BaseVariable* variable);

    void malloc(Variables::BaseVariable* var);

    bool is_program_variable(Variables::BaseVariable* var);

    Variables::BaseVariable* get_variable_by_name_hint(std::string const & name_hint);

    Variables::BaseVariable* get_variable_by_mem_pos(int const mem_pos);

    bool var_exists(std::string const & var);

    void dump(std::ostream & stream = std::cout);

    std::vector<Variables::BaseVariable*> get_variables();

    std::vector<Variables::BaseVariable*> get_free_variables();
    void update_free_variables(Variables::BaseVariable* var);

    std::vector<Variables::BaseVariable*> get_select_variables();
    
    Variables::BaseVariable* get_last_added_variable();

    size_t get_last_used_address();

    int address_offset_to_mem_address(Variables::BaseVariable* pointer,
                                      int const address_offset);

    void clean_memory(std::string const & sourcefile,
                      std::string const & function,
                      std::list<std::string> const & blacklist);

    void free(Variables::BaseVariable* var);
    
    void memcpy(Variables::PointerVariable* src,
                Variables::PointerVariable* dst,
                size_t const bytes);
    
    void memset(Variables::PointerVariable* dst,
                size_t const  val,
                size_t const bytes);
    
private:
    Memory(z3::context* z3_ctx);
    virtual ~Memory();

    friend class MemoryExporter;

    static Memory* p_instance;
    static bool p_singleton;

    z3::context * p_z3_ctx;

    std::map<size_t, Variables::BaseVariable*> p_variables;
    std::map<size_t, Variables::BaseVariable*> p_memory;
    std::map<size_t, Variables::BaseVariable*> p_heap;
    
    std::vector<Variables::BaseVariable*> p_free_variables;
    
    size_t MEMORYSIZE;
    std::map<std::string, size_t> p_name_2_array_pos;
    size_t p_alloc_pointer;
    size_t p_heap_pointer;
    size_t p_variable_pointer;
    size_t p_last_address_in_use;
   
    Logger* p_logger;
    Database* p_database;

    Variables::BaseVariable* deref_pointer(Variables::BaseVariable* var);
    void check_free(Variables::BaseVariable* var);
    std::vector<Variables::BaseVariable*> check_memory_leaks();
    bool clean_memory_blacklisted(Variables::BaseVariable* var,
                                  std::list<std::string> const & blacklist);
    void flush();
};

}

#endif /* YASSI_MEMORY_HPP */
