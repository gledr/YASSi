/** 
 * @file yassi_basevariable.hpp
 * @brief Virtual Base Variable Type for Symbolic Execution
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
#ifndef YASSI_BASEVARIABLE_HPP
#define YASSI_BASEVARIABLE_HPP

#include <string>
#include <vector>
#include <cstdint>
#include <iterator>
#include <set>

#include <z3++.h>

#include <yassi_exception.hpp>
#include <yassi_types.hpp>
#include <yassi_baseutils.hpp>
#include <yassi_utils.hpp>

namespace Yassi::Backend::Execute::Variables {

enum eSign {
    eUnknown,  ///< Sign Not Resolved - Unknown
    eUnsigned, ///< Sign Resolved - Unsigned 
    eSigned    ///< Signed Resolved - Signed
};

enum eAllocationType {
    eUnallocated   = 0, ///< Variable Unallocated
    eStack         = 1, ///< Variable on Stack
    eHeapAllocated = 2, ///< Variable on Heap Active
    eHeapFreed     = 3  ///< Variable on Stack Freed
};

/**
 * @class BaseVariable
 * @brief Virtual Base Variable for Symbolic Execution 
 */
class BaseVariable {
public:

    virtual ~BaseVariable();

    void set_name_hint(std::string const & hint);
    std::string get_name_hint();

    void set_name(std::string const & name);
    std::string get_name();

    void unset_free_variable();
    bool is_free_variable();

    void set_force_free();
    bool is_forced_free();

    bool used();

    bool is_constant();
    void set_constant();
    void unset_constant();

    bool is_global();
    void set_global();

    void set_lastaddress(size_t const lastaddress);
    size_t get_lastaddress();

    void set_firstaddress(size_t const firstaddress);
    size_t get_firstaddress();

    std::string get_value_as_string();

    uint64_t get_value_ui64();
    int64_t  get_value_i64();

    uint32_t get_value_ui32();
    int32_t  get_value_i32();

    uint16_t get_value_ui16();
    int16_t  get_value_i16();

    uint8_t get_value_ui8();
    int8_t  get_value_i8();

    void set_sourcefile(std::string const & sourcefile);
    std::string get_sourcefile();

    void set_function(std::string const & function);
    std::string get_function();

    double get_value_double_precision();
    float get_value_single_precision();

    bool get_value_bool();

    void set_type(Yassi::Types::BaseType* next_type);
    Yassi::Types::BaseType* get_type();

    bool is_propaged_constant();
    void set_propagated_constant();

    BaseVariable* get_propagated_from();
    void set_propagated_from(BaseVariable* var);

    void set_value(std::string next_value);
    void set_value_free_variable(std::string const & next_value);

    eSign get_sign();
    void set_sign(eSign const sign);

    void set_smt_formula(z3::expr new_variable);
    void clear_smt_formula();

    void set_index_assertion(z3::expr assertion);
    z3::expr get_index_assertion();
    bool has_index_assertion();

    bool get_comes_from_nonannotated();
    void set_comes_from_nonannoated(bool const val);

    bool get_is_linear();
    void set_is_linear(bool const val);

    size_t get_alloc_point();
    void set_alloc_point(size_t const val);

    bool is_function_pointer();
    void set_funtion_pointer(bool const fp);

    void insert_index(std::vector<size_t> const & val);
    std::vector<std::vector<size_t>> get_index_values();
    bool has_indexes();
    void clear_indexes();
    
    void set_index_alignment(std::vector<std::pair<size_t, size_t>> const & alignment);
    std::vector<std::pair<size_t, size_t>> get_index_alignment();

    void add_index_base_pointer(BaseVariable* ptr);
    std::vector<BaseVariable*> get_index_base_pointer();
    void clear_index_base_pointer();

    void add_index_var(BaseVariable* var);
    std::vector<BaseVariable*> get_index_var();
    void clear_index_var();

    void set_allocation_type(eAllocationType const alloc_type);
    eAllocationType get_allocation_type();

    void set_offset_tree(std::string const & offset_tree);
    std::string get_offset_tree();
    bool has_offset_tree();

    virtual z3::expr get_smt_formula() = 0;
    virtual z3::expr get_formula_to_evaluate() = 0;

    virtual void dump(std::ostream & stream = std::cout) = 0;

    void set_parent(BaseVariable* ptr);
    BaseVariable* get_parent();

    virtual void set_pointer(BaseVariable* dst) = 0;
    virtual BaseVariable* get_pointer() = 0;

    eAllocationType getPAllocationType() const;

protected:

    BaseVariable(z3::context* z3_ctx);

    Yassi::Types::BaseType* p_type;// The Type 
    std::string p_name_hint;        // The Name used within LLVM
    std::string p_name;             // The Unique Name Used with SMT2
    std::string p_value;            // The current value
    bool p_free_variable;           // Free Value aca has never been assigned
    eSign p_sign;
    bool p_force_free;              // Value forced to be free
    bool propageted_constant;       // 
    bool p_constant;                // Indicates if the variable is a constant
    bool p_global;
    bool p_linear;                  // Indicates if the variable is linear (propagated only from constants)
    size_t p_firstaddress;
    size_t p_lastaddress;
    size_t p_alloc_point;
    bool p_function_pointer;
    BaseVariable* p_propagated_from;
    z3::expr p_smt_formula;
    bool p_obsolete_smt_formula;
    BaseVariable* p_pointer;
    BaseVariable* p_parent;
    bool p_comes_from_nonannotated;
    eAllocationType  p_allocation_type;

    std::string p_source_file;
    std::string p_function;

    std::string p_offset_tree;

    // All possible index values which are possible to dereference the pointer
    std::vector<std::vector<size_t>> p_index_values; 
    std::vector<std::pair<size_t, size_t>> p_index_alignment;
    std::vector<BaseVariable*> p_index_variable;
    std::vector<BaseVariable*> p_index_base_pointer;
    bool p_has_index_assertion;
    z3::expr p_index_assertion;
    z3::context * p_z3_ctx;
};

}

#endif /* YASSI_BASEVARIABLE_HPP */
