/** 
 * @file yassi_object.hpp
 * @brief Virtual Base Class for the Yassi Frontend
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
#ifndef YASSI_FRONTEND_OBJECT_HPP
#define YASSI_FRONTEND_OBJECT_HPP

#include <string>
#include <vector>

#include <yassi_database.hpp>
#include <yassi_utils.hpp>

namespace Yassi::Frontend {

class Database;

/**
 * @class Object
 * @brief Virtual Base Class for the Yassi Frontend
 */
class Object {
public:
    virtual ~Object();

protected:
    Object();

    static std::string get_src_dir();
    static std::string get_bin_dir();
    static std::string get_db_dir();
    static std::string get_img_dir();
    static std::string get_smt_dir();
    static std::string get_log_dir();

    static std::string get_cxx();
    static std::string get_opt();
    static std::string get_dis_asm();

    static void set_tmp_folder(std::string const & path);
    static std::string get_tmp_folder();

    static void set_editor(std::string const & editor);
    static std::string get_editor();

    static  void set_image_viewer(std::string const & viewer);
    static  std::string get_image_viewer();

    static  void set_compare_tool(std::string const & tool);
    static std::string get_compare_tool();

    static void set_source_files(std::vector<std::string> const & files);
    static std::vector<std::string> get_source_files();
    
    static void set_base_path(std::string const & path);
    static std::string get_base_path();

    static void set_modelcheck_backend_name(std::string const & name);
    static std::string get_modelcheck_backend_name();

    static void set_replay_backend_name(std::string const & name);
    static std::string get_replay_backend_name();

    static std::string get_execution_url();
    static void set_execution_url(std::string const & url);

    static bool get_debug();
    static void set_debug(bool val);

    static size_t get_max_depth();
    static void set_max_depth(size_t const depth);

    static std::string get_bughunter_binary_name();
    static void set_bughunter_binary_name(std::string const & name);
    
    static bool get_quiet();
    static void set_quiet(bool const mode);

    static bool get_log_file_enabled();
    static void set_log_file_enabled(bool val);

    static bool get_dump_memory();
    static void set_dump_memory(bool const val);

    static bool get_dump_smt();
    static void set_dump_smt(bool const val);

    static size_t get_timeout();
    static void set_timeout(size_t const to);

    static std::string get_logfile_name();
    static void set_logfile_name(std::string const & name);

    static std::string get_isolate_function();
    static void set_isolate_function(std::string const & function);
    static bool has_seed_function();

    Database* p_database;

private:
    Object(Object const & obj);
    bool operator== (Object const & obj);
    Object& operator= (Object const & obj);

    static std::string p_tmp_folder;                ///<
    static std::string p_editor;                    ///<
    static std::string p_image_viewer;              ///<
    static std::string p_compare_tool;              ///<
    static std::string p_base_path;                 ///<
    static std::string p_modelcheck_backend_name;   ///<
    static std::string p_replay_backend_name;       ///<
    static std::string p_bughunter_backend_name;    ///<
    static std::string p_current_url;               ///<
    static std::string p_logfile_name;              ///<
    static std::string p_seed_function;             ///<
    static bool p_debug;                            ///<
    static bool p_quiet;                            ///<
    static bool p_log_file_enabled;                 ///<
    static bool p_dump_smt;                         ///<
    static bool p_dump_memory;                      ///<
    static size_t p_max_depth;                      ///<
    static size_t p_timeout;                        ///<
    static std::vector<std::string> p_source_files; ///<
};

}

#endif /* YASSI_FRONTEND_OBJECT_HPP */
