/** 
 * @file yassi_memoryexporter.cpp
 * @brief Yassi Execution Memory Exporter to JSON
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
#include "yassi_memoryexporter.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;


/**
 * @brief
 * 
 * @param z3_ctx
 */
MemoryExporter::MemoryExporter(z3::context* z3_ctx)
{
    p_z3_ctx = z3_ctx;
    p_memory = Memory::getInstance(p_z3_ctx);
}

/**
 * @brief
 */
MemoryExporter::~MemoryExporter()
{
    p_memory = nullptr;
}

/**
 * @brief ...
 */
void MemoryExporter::export_memory()
{
    std::string url = this->get_execution_url() + "/memory_dump.json";
    
    if(access(url.c_str(), F_OK) != -1){
        remove(url.c_str());
    }
    
    std::fstream outfile(url, std::ios::out);
    
    Json::Value root;
    
    for(size_t i = 0; i < p_memory->p_alloc_pointer; ++i){
        Json::Value tmp;
        BaseVariable* variable = p_memory->p_memory[i];
                
        tmp["name"] = variable->get_name();
        if(variable->get_name_hint() != ""){
            tmp["name_hint"] = variable->get_name_hint();
        } else {
            tmp["parent_name"] = variable->get_parent()->get_name_hint();
        }
        
        tmp["force_free"] = std::to_string(variable->is_forced_free());
        tmp["free_variable"] = std::to_string(variable->is_free_variable());
        tmp["value"] = variable->get_value_as_string();
        tmp["type"] = variable->get_type()->get_type_identifier();
        tmp["constant"] = std::to_string(variable->is_constant());
        
        if(variable->get_type()->is_pointer()){
            PointerVariable* ptr_var = dynamic_cast<PointerVariable*>(variable);
            if(ptr_var->get_pointer() != nullptr){
                tmp["pointer"] = ptr_var->get_pointer()->get_name();
            } else {
                tmp["pointer"] = "NULL";
            }
        }
        tmp["first_address"] = std::to_string(variable->get_firstaddress());
        tmp["last_address"] = std::to_string(variable->get_lastaddress());
     
        //if (variable->is_propaged_constant() && variable->get_propaged_from().size() > 0){
        //    tmp["propagated_from"] = variable->get_propaged_from().front()->get_name();
        //}
        
        tmp["smt"] = variable->get_smt_formula().to_string();
        tmp["linear"] = variable->get_is_linear() ? "true" : "false";
    
        root.append(tmp);
    }
    
    outfile << root;
    outfile.close();
}
