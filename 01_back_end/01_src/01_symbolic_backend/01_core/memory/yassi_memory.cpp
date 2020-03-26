/** 
 * @file yassi_memory.cpp
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
#include "yassi_memory.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;

/**
 * Static Singleton Pattern Infrastructure
 */ 
bool Memory::p_singleton = false;
Memory* Memory::p_instance;

/**
 * @brief Singleton Pattern Access-Function
 * 
 * @return Yassi::Memory*
 */
Memory* Memory::getInstance(z3::context* z3_ctx)
{
    /* No NullPointer Check here - can be null */
    
    if(Memory::p_singleton == false){
        Memory::p_instance = new Memory(z3_ctx);
        Memory::p_singleton = true;
    }
    return Memory::p_instance;
}

/**
 * @brief Destroy Singleton Pattern Instance
 */
void Memory::destroy()
{
    delete Memory::p_instance;  p_instance = nullptr;
    Memory::p_singleton = false;
}

/**
 * @brief Constructor - Called by the Singleton Pattern Access Function
 */
Memory::Memory(z3::context* z3_ctx):
    Object()
{
    p_z3_ctx = z3_ctx;
    p_database = new Database(this->get_database_url());
    p_logger = Logger::getInstance();

    p_heap_pointer = 0;
    p_alloc_pointer = 0;
    p_variable_pointer = 0;
    p_last_address_in_use = 0;
}

/**
 * @brief Destructor
 */
Memory::~Memory()
{
    delete p_database; p_database = nullptr;
    this->flush();
}

/**
 * @brief Allocate an internal llvm variable
 * 
 * Variable is getting directly allocated as is - no extra pointer used.
 * 
 * @param variable: The existing variable to be added to the memory.
 */
void Memory::alloc_llvm_variable(BaseVariable* variable)
{
    nullpointer_check(variable);

    variable->set_allocation_type(eStack);

    p_memory[p_alloc_pointer] = variable;

    if(p_alloc_pointer == 0){
        variable->set_firstaddress(0);
        size_t lastaddr = variable->get_type()->get_bytes()-1;
        variable->set_lastaddress(lastaddr);
        p_last_address_in_use = lastaddr;
    } else {
        variable->set_firstaddress(p_last_address_in_use + 1);
        size_t last_addr = p_last_address_in_use + variable->get_type()->get_bytes();
        variable->set_lastaddress(last_addr);
        p_last_address_in_use = last_addr;
    }

    variable->set_alloc_point(p_alloc_pointer);
    variable->set_name("mem_" + std::to_string(p_alloc_pointer));
    
    if(variable->get_name_hint() != ""){
        p_name_2_array_pos[variable->get_name_hint()] = p_alloc_pointer;
    }
    p_alloc_pointer++;
}

/**
 * @brief Allocate a Program Variable (As used in the C/C++ Code)
 * 
 * Therefore a pointer to the variable is inserted in a datastructure 
 * and the variable itself is added to the memory. 
 * 
 * @param obj_ptr: The pointer to the variable
 * @param variable: The C/C++ variable
 */
void Memory::alloc_program_variable(PointerVariable* obj_ptr,
                                    BaseVariable* variable)
{
    if(obj_ptr == nullptr){
        this->alloc_llvm_variable(variable);
        p_variables[p_variable_pointer] = variable;
    } else {
        nullpointer_check(variable);
        
        this->alloc_llvm_variable(variable);
        this->update_free_variables(variable);
     
        obj_ptr->set_pointer(variable);
        variable->set_parent(obj_ptr);
        obj_ptr->set_name("var_" + std::to_string(p_variables.size()));
        obj_ptr->set_alloc_point(p_variables.size());
        p_variables[p_variable_pointer] = obj_ptr;
    }
    p_variable_pointer++;
}

/**
 * @brief
 *
 * @param var
 */
void Memory::malloc(BaseVariable* var)
{
    nullpointer_check(var);

    var->set_allocation_type(eHeapAllocated);
    p_memory[p_alloc_pointer] = var;
    var->set_firstaddress(p_memory[p_alloc_pointer-1]->get_lastaddress() + 1);
    size_t last_addr = p_memory[p_alloc_pointer-1]->get_lastaddress() + var->get_type()->get_bytes();
    var->set_lastaddress(last_addr);
    p_heap[p_heap_pointer] = var;

    var->set_name_hint("heap_" + std::to_string(p_heap_pointer));
    var->set_alloc_point(p_alloc_pointer);
    var->set_name("mem_" + std::to_string(p_alloc_pointer));

    this->update_free_variables(var);
    
    p_alloc_pointer++;
    p_heap_pointer++;
}

/**
 * @brief Get access to the polymorph BaseVariable pointer of a variable stored in the memory
 * 
 * @param name_hint p_name_hint: The name_hint of the variable
 * @return Yassi::BaseVariable*
 */
BaseVariable* Memory::get_variable_by_name_hint(std::string const & name_hint)
{
    try {
        BaseVariable *retval;
        // Check if internal llvm variable
        bool exists = false;

        for(auto itor = p_variables.rbegin(); itor != p_variables.rend(); ++itor){
            if (itor->second->get_name_hint().compare(name_hint) == 0) {
                exists = true;
                retval = itor->second;
                break;
            }
        }

        if (!exists) {
            for(auto itor = p_memory.rbegin(); itor != p_memory.rend(); ++itor){
                if (itor->second && itor->second->get_name_hint().compare(name_hint) == 0) {
                    exists = true;
                    retval = itor->second;
                    break;
                }
            }
        }

        // Throw an execption if the variable has not been found finally
        if (!exists) {
            assert (0);
            std::string msg = "Variable (" + name_hint + ") has not been found!";
            throw YassiException(msg);
        }

        nullpointer_check(retval);
        
        return retval;
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief Get access to the free variables used in the program
 * 
 * @return std::vector< Yassi::BaseVariable* >
 */
std::vector<BaseVariable *> Memory::get_free_variables()
{
    return p_free_variables;
}

/**
 * @brief Keep track of the free variables availible in the code
 * 
 * @param var: Modified Variable to check
 */
void Memory::update_free_variables(BaseVariable* var)
{
    nullpointer_check(var);
    bool debug = false;
   
    if(var->is_constant() || var->is_propaged_constant()){
        return;
    } 

    auto val = std::find_if(p_free_variables.begin(),
                            p_free_variables.end(),
                            [&](BaseVariable* x) {
                                return x->get_name() == var->get_name();
                            });
    if(val != p_free_variables.end()){
        if((!var->is_forced_free()) && (!var->is_free_variable())){
            p_free_variables.erase(val);
            debug && std::cout << "Erase: " << var->get_name() << " from free_variables" << std::endl; 
        }
    } else {
        if(var->is_forced_free() || var->is_free_variable()){
            p_free_variables.push_back(var);
            debug && std::cout << "Insert: " << var->get_name() << " to free_variables" << std::endl;
        }
    }
}

/**
 * @brief Get Access to all stored Variables
 * 
 * @return std::vector< Yassi::BaseVariable* >
 */
std::vector<BaseVariable*> Memory::get_variables()
{
    std::vector<BaseVariable*> retval;

    for(size_t i = 0 ; i < p_variable_pointer; ++i){
        if(p_variables[i]->get_type()->is_pointer()){
            nullpointer_check(p_variables[i]->get_pointer());
            retval.push_back(p_variables[i]->get_pointer());
        } else {
            /* Return Values from NonAnnotated Function Calls are not stored
             * using a Pointer
             */
            retval.push_back(p_variables[i]);
        }
    }
    return retval;
}

/**
 * @brief
 * 
 * @return std::vector< Yassi::BaseVariable* >
 */
std::vector<BaseVariable *> Memory::get_select_variables()
{
    std::vector<BaseVariable*> select_variables;
    
    for(auto& itor : p_variables){
        if(itor.second->get_name_hint().find("select_enable") != std::string::npos){
            PointerVariable* ptr_var = dynamic_cast<PointerVariable*>(itor.second);
            select_variables.push_back(ptr_var->get_pointer());
        }
    }
    return select_variables;
}

/**
 * @brief Shows the current elements in the memory 
 */
void Memory::dump(std::ostream & stream)
{
    for(size_t i = 0; i < p_alloc_pointer; ++i){
        stream << "NameHint: " << p_memory[i]->get_name_hint() 
               << " Type: " << p_memory[i]->get_type()->get_type_identifier()
               << " " << p_memory[i]->get_smt_formula().get_sort().to_string() << " " 
               << " Value: " << p_memory[i]->get_value_as_string()
               << " FreeVariable: " <<  p_memory[i]->is_free_variable() << std::endl;
               
        if(p_memory[i]->get_type()->is_pointer()){
            PointerVariable* ptr_var = dynamic_cast<PointerVariable*>(p_memory[i]);
            ptr_var->dump();
        }
    }
}

/**
 * @brief Checks if a variable has been allocated or not
 * 
 * Used in order to check if a function pointer has been allocated 
 * 
 * @param var The variable to check
 * @return bool
 */
bool Memory::var_exists(const std::string& var) 
{
    bool is_program_variable = false;

    for(auto& itor: p_variables){
        if(itor.second != nullptr){
            if (itor.second->get_name_hint() == var) {
                is_program_variable = true;
                break;
            }
        }
    }
    return (p_name_2_array_pos.find(var) != p_name_2_array_pos.end()) || is_program_variable;
}

/**
 * @brief
 * 
 * @param mem_pos:
 * @return Yassi::BaseVariable*
 */
BaseVariable* Memory::get_variable_by_mem_pos(int const mem_pos) 
{
    nullpointer_check(p_memory[mem_pos]);
    return p_memory[mem_pos];
}

/**
 * @brief Get the alloc position by a base pointer and an offset
 * 
 * Used in order to calculate the static getelementptr destination
 * 
 * @param pointer p_pointer: The pointer used as base pointer
 * @param _address_offset p__address_offset: The offset in byte to be added to
 * @return int 
 */
int Memory::address_offset_to_mem_address(BaseVariable* pointer,
                                          int const _address_offset)
{
    int start = pointer->get_alloc_point();
    int address_offset = _address_offset;
    int step = start;

    while(address_offset > 0){
        BaseVariable* elem = p_memory[step];
        nullpointer_check(elem);

        int bytes = elem->get_type()->get_bytes();
        address_offset -= bytes;
        step++;
    }

    return step;
}

/**
 * @brief Get last address of last byte allocated in the memory
 * 
 * @return size_t
 */
size_t Memory::get_last_used_address() 
{
    return p_memory[p_alloc_pointer-1]->get_lastaddress();
}

/**
 * @brief Shows if the variable is used in the C code and therefore has its own pointer
 * 
 * @param var: The variable to checked
 */ 
bool Memory::is_program_variable(BaseVariable* var)
{
    for(auto itor : p_variables){
        if(itor.second == var){
            return true;
        }
    }
    return false;
}

/**
 * @brief Delete allocated variable objects which are out of scope
 *
 * @param sourcefile: The source file currently executed
 * @param function: The function scope just ended
 * @param blacklist: The variables to keep alive
 */
void Memory::clean_memory(std::string const & sourcefile,
                          std::string const & function,
                          std::list<std::string> const & blacklist)
{
    return;
    std::set<BaseVariable*> delete_me;
    
    for(size_t i = 0; i < p_alloc_pointer; ++i){
        if(p_memory[i] != nullptr && p_memory[i]->get_allocation_type() == eStack){
            BaseVariable* tmp = p_memory[i];
            
           if(tmp->get_parent() != nullptr && tmp->get_parent()->is_global()){
               continue;
           }
            
            if((tmp->get_sourcefile().compare(sourcefile) == 0) 
                && (tmp->get_function().compare(function) == 0)){
                if(tmp->get_parent() != nullptr &&
                    this->is_program_variable(tmp->get_parent())){
                    if(!this->clean_memory_blacklisted(tmp->get_parent(), blacklist)){
                        BaseVariable* parent = tmp->get_parent();

                        if (!tmp->is_free_variable()){
                            delete_me.insert(tmp);
                            delete_me.insert(parent);
                            
                            tmp->set_parent(nullptr);
                            //parent->set_pointer(nullptr);
                            p_variables[parent->get_alloc_point()] = nullptr;
                            p_variables.erase(parent->get_alloc_point());
                            
                            p_name_2_array_pos[tmp->get_name_hint()] = 0;
                            p_name_2_array_pos.erase(tmp->get_name_hint());
                            

                            p_memory[tmp->get_alloc_point()] = nullptr;
                            p_memory.erase(tmp->get_alloc_point());
                               
                            p_logger->clean_stack_variable(parent);
                            p_logger->clean_stack_variable(tmp);

                            delete tmp; tmp = nullptr;
                            delete parent; parent = nullptr;
                        }
                    }
                } else {
                    if(!this->clean_memory_blacklisted(tmp, blacklist)){
                        if (!tmp->is_free_variable()) {
                            p_name_2_array_pos[tmp->get_name_hint()] = 0;
                            p_name_2_array_pos.erase(tmp->get_name_hint());
                            p_memory[tmp->get_alloc_point()] = nullptr;
                            p_memory.erase(tmp->get_alloc_point());
                            
                            p_logger->clean_stack_variable(tmp);
                            
                            delete tmp; tmp = nullptr;
                        }
                    }
                }
            }
        }
    }
}

/**
 * @brief Check if variable is blacklisted from removing
 *
 * @param var: The variable to check for blacklist
 * @param blacklist: The blacklist to be applied
 *
 * @return True if blacklisted, else false.
 */
bool Memory::clean_memory_blacklisted(BaseVariable* var,
                                      std::list<std::string> const & blacklist)
{
    for(auto itor: blacklist){
        if(var->get_name_hint().compare(itor) == 0){
            return true;
        }
    }
    return false;
}

BaseVariable* Memory::get_last_added_variable()
{
    return p_variables.end()->second;
}

/**
 * @brief Delete all variables in memory against memory leaks
 */
void Memory::flush()
{
    std::set<BaseVariable*> delete_me;

    for(size_t i = 0; i < p_alloc_pointer; ++i){
        if(p_memory[i] != nullptr) {
            BaseVariable* tmp = p_memory[i];

            if(tmp->get_parent() != nullptr && this->is_program_variable(tmp->get_parent())){
                BaseVariable* parent = tmp->get_parent();
                delete_me.insert(tmp);
                delete_me.insert(parent);
            } else {
                delete_me.insert(tmp);
            }
        }
    }

    for(auto itor: delete_me){
       delete itor; itor = nullptr;
    }
}

/**
 * @brief Check for Possible Memory Leaks in the Heap
 * 
 * @return std::vector< Yassi::BaseVariable* >
 */
std::vector<BaseVariable*> Memory::check_memory_leaks()
{
    std::vector<BaseVariable*> leaks;
    
    for(auto itor: p_heap){
        if(itor.second->get_allocation_type() == eHeapAllocated){
            leaks.push_back(itor.second);
        }
    }
    return leaks;
}

/**
 * @brief Release Heap Allocated Memory
 *
 * @param var: The variable to release
 */
void Memory::free(BaseVariable* var)
{
    BaseVariable* first_elem = var->get_pointer();

    size_t last_addr = first_elem->get_lastaddress();
    size_t alloc_point = first_elem->get_alloc_point();

    p_memory[alloc_point]->set_allocation_type(eHeapFreed);
    alloc_point++;

    while(last_addr >= p_memory[alloc_point]->get_lastaddress()){
        this->check_free(p_memory[alloc_point]);
        p_memory[alloc_point]->set_allocation_type(eHeapFreed);
        alloc_point++;
    }
}

/**
 * @brief
 * 
 * @param var:
 */
void Memory::check_free(BaseVariable* var)
{
    nullpointer_check(var);
    
    if(var->get_allocation_type() != eHeapAllocated){
        p_logger->exception_found(e_double_free,
                                  this->get_file_being_executed(),
                                  std::to_string(this->get_line_num_execution()),
                                  "");
        
        p_database->insert_exception(e_double_free,
                                     Object::get_file_being_executed(),
                                     std::to_string(Object::get_line_num_execution()));
        
        p_database->insert_error_trace(this->get_path_history());
        p_logger->terminate_backend();
        kill(0, SIGKILL);
    }
}

/**
 * @brief Copy a Block of Memory
 * 
 * @param src Pointer to Source
 * @param dst Pointer to Destination
 * @param bytes Bytes to Copy
 */
void Memory::memcpy(Variables::PointerVariable* src,
                    Variables::PointerVariable* dst,
                    size_t const bytes)
{
    nullpointer_check(src);
    nullpointer_check(dst);

    BaseVariable* src_element = this->deref_pointer(src);
    BaseVariable* dst_element = this->deref_pointer(dst);
    
    nullpointer_check(src_element);
    nullpointer_check(dst_element);
    
    /*
     * NOTE: We can not use the size_bytes used within LLVM
     * since those bytes are according to the internal LLVM memory alignment!
     */

    size_t bytes_total = src_element->get_lastaddress() - src_element->get_firstaddress() + 1;
    assertion_check (bytes_total <= bytes);

    size_t bytes_done = 0;

    while(bytes_done < bytes_total){

        size_t src_pos = src_element->get_alloc_point();
        size_t dst_pos = dst_element->get_alloc_point();

        //assertion_check (src_element->get_type() == dst_element->get_type()); FIXME

        dst_element->set_value(src_element->get_value_as_string());
        dst_element->set_smt_formula(src_element->get_smt_formula());
        this->update_free_variables(dst_element);

        bytes_done += src_element->get_type()->get_bytes();
        
        src_element = this->get_variable_by_mem_pos(src_pos+1);
        dst_element = this->get_variable_by_mem_pos(dst_pos+1);
    }
}

/**
 * @brief Set a Block Memory to a Specific Value
 * 
 * @param dst Pointer to the Destination
 * @param val Value to be applied
 * @param bytes Bytes to be set
 */
void Memory::memset(Variables::PointerVariable* dst,
                    size_t const val,
                    size_t const bytes)
{
    notimplemented_check();
}

/**
 * @brief Dereference a Pointer
 * 
 * @param var Pointer
 * @return Yassi::Backend::Execute::Variables::BaseVariable*
 */
Variables::BaseVariable* Memory::deref_pointer(BaseVariable* var)
{
    assert (var != nullptr);
    
    if(var->get_type()->is_pointer() && var->get_pointer() != nullptr){
        this->deref_pointer(var->get_pointer());
    } else {
        return var;
    }
}
