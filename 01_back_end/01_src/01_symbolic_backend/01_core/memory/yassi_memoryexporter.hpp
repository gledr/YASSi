/** 
 * @file yassi_memoryexporter.hpp
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
#ifndef YASSI_MEMORYEXPORTER_HPP
#define YASSI_MEMORYEXPORTER_HPP

#include <memory>
#include <json/json.h>
#include <fstream>

#include <yassi_object.hpp>
#include <yassi_memory.hpp>

#include <z3++.h>

namespace Yassi::Backend::Execute {

/**
 * @class MemoryExporter
 * @brief Export the Execution Memory to JSON for Debugging
 */
class MemoryExporter: public virtual Object {
public:
    MemoryExporter(z3::context* z3_ctx);
    
    virtual ~MemoryExporter();
    
    void export_memory();
    
private:
    Memory* p_memory;
    z3::context* p_z3_ctx;
    
    friend class Memory;
    
};

}

#endif /* YASSI_MEMORYEXPORTER_HPP */
