/** 
 * @file yassi_bitcode.hpp
 * @brief Class used for Compile, Instrument, Visualize Bitcode
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
#ifndef YASSI_BITCODE_HPP
#define YASSI_BITCODE_HPP

#include <regex>

#include <yassi_object.hpp>
#include <yassi_logger.hpp>
#include <yassi_common.hpp>
#include <yassi_exception.hpp>

#include <boost/range.hpp>
#include <boost/filesystem.hpp>

namespace Yassi::Frontend {

/**
 * @class Bitcode
 * @brief Generic LLVM Bitcode handler
 *
 * Class used for Compile, Instrument, Visualize Bitcode
 */
class Bitcode: public virtual Object {
public:
    Bitcode();

    virtual ~Bitcode();

    void generate_bitcode();

    void show_bitcode();

    void show_cfg();

    void show_bb();

    void list_external_functions();

protected:
    void show_cfg_common();

    Logger* p_logger;
    Common* p_common;

    /**
     * @brief Make Disassembled Name for Original Code
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_first_ll(std::string const & filename)
    {
        return filename + ".ll";
    }

    /**
     * @brief Make Bitcode Name after first instrumentation
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_second_bc(std::string const & filename)
    {
        return filename + "-1.bc";
    }

    /**
     * @brief Make Disassembled Name after first instrumentation
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_second_ll(std::string const & filename)
    {
        return filename + "-1.ll";
    }

    /**
     * @brief Make Bitcode Name after second instrumentation
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_third_bc(std::string const & filename)
    {
         return filename + "-2.bc";
    }

    /**
     * @brief Make Disassembled Name after second instrumentation
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_third_ll(std::string const & filename)
    {
        return filename + "-2.ll";
    }
    
    /**
     * @brief Make Object-File Name after third instrumentation
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_fourth_obj(std::string const & filename)
    {
        return filename + "-3.o";
    }
    
    /**
     * @brief Make Bitcode Name after third instrumentation
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_fourth_bc(std::string const & filename)
    {
         return filename + "-3.bc";
    }

    /**
     * @brief Make Disassembled Name after third instrumentation
     * 
     * @param filename Sourcefile Name
     * @return std::string
     */
    inline std::string make_fourth_ll(std::string const & filename)
    {
        return filename + "-3.ll";
    }

private:
    void check_recursive();

    std::string INTRINSICS_HEADER;
};

}

#endif /* YASSI_BITCODE_HPP */
