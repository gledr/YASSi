/** 
 * @file yassi_common.cpp
 * @brief Yassi Common acts as collection of supporting Tools
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
#include "yassi_common.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
Common::Common():
    Object()
{
    p_logger = Logger::getInstance();
}

/**
 * @brief Destructor
 */
Common::~Common()
{
    p_logger = nullptr;
}

/**
 * @brief Clean Temporary Directory
 */
void Common::clean_environment()
{
    boost::filesystem::remove_all(this->get_tmp_folder());

    if(!boost::filesystem::create_directory(this->get_tmp_folder())){
        throw YassiException("Could not create yassi directory!");
    }
    if(!boost::filesystem::create_directory(this->get_db_dir())){
        throw YassiException("Could not create db directory!");
    }
    if(!boost::filesystem::create_directory(this->get_src_dir())){
        throw YassiException("Could not create src directory!");
    }
    if(this->get_dump_smt()){
        if(!boost::filesystem::create_directory(this->get_smt_dir())){
            throw YassiException("Could not create SMT2 directory!");
        }
    }
    if(boost::filesystem::exists(this->get_execution_url() + "/" + this->get_logfile_name())){
        boost::filesystem::remove(this->get_execution_url() + "/" + this->get_logfile_name());
    }
    if(!boost::filesystem::create_directory(this->get_log_dir())){
        throw YassiException("Could not create log directory!");
    }
    p_database->init_db();
    p_database->insert_option("verbose", this->get_debug() == false ? "false" : "true");
    p_database->insert_option("log_file_enabled", this->get_log_file_enabled() == false ? "false" : "true");
    p_database->insert_option("timeout", std::to_string(this->get_timeout()));
    p_database->insert_option("dump_smt", this->get_dump_smt() == true ? "true" : "false");
    p_database->insert_option("logfile_name", this->get_logfile_name());
    p_database->insert_option("quiet", this->get_quiet() == false ? "false" : "true");
    this->check_external_tools();
}

/**
 * @brief Call Sqlitebrowser and show Database Content
 */
void Common::show_db()
{
    std::vector<std::string> cmd_args;
    cmd_args.push_back(this->get_db_dir() + "database.db");
    
    this->system_execute("sqlitebrowser", cmd_args, "", false);
}

/**
 * @brief Check if all needed external tools are availible
 */
void Common::check_external_tools()
{
    // Check clang++
    if(!boost::filesystem::exists(this->get_cxx())){
        throw YassiException("Can not find the clang++ Compiler!");
    }

    // Check opt
    if(!boost::filesystem::exists(this->get_opt())){
        throw YassiException("Can not find the LLVM Optimization Tool!");
    }

    // Check llvm-dis
    if(!boost::filesystem::exists(this->get_dis_asm())){
        throw YassiException("Can not find the LLVM Disassably Tool!");
    }

    // Check editor
    if(!boost::filesystem::exists(boost::process::search_path(this->get_editor()))){
        throw YassiException("Can not find the configured editor! (" + this->get_editor() + ")");
    }

    // Check Compare Tool
    if(!boost::filesystem::exists(boost::process::search_path(this->get_compare_tool()))){
        throw YassiException("Can not find the configured compare tool! (" + this->get_compare_tool() + ")");
    }

    // Check Image Viewer
    if(!boost::filesystem::exists(boost::process::search_path(this->get_image_viewer()))){
        throw YassiException("Can not find the configured image viewer! (" + this->get_image_viewer() + ")");
    }

    // Check cflow
    if(!boost::filesystem::exists(boost::process::search_path("cflow"))){
        p_logger->cflow_not_found();
    }
}

/**
 * @brief Execute a Tool on the Host System
 * 
 * @param binary Name of the binary
 * @param args Command line arguments
 * @param output Path for the logfile
 * @param wait_for_termination: Wait until the subprocess has terminated
 * @return int
 */
int Common::system_execute(std::string const & binary, std::vector<std::string> & args, std::string const & output, bool wait_for_termination)
{
    int pid;
    return this->system_execute(binary, args, output, pid, wait_for_termination);
}

/**
 * @brief Execute a Tool on the Host System
 * 
 * @param binary Name of the binary
 * @param args Command line arguments
 * @param output Path for the logfile
 * @param pid: Pid of the current subprocess 
 * @param wait_for_termination: Wait until the subprocess has terminated.
 * @return int
 */
int Common::system_execute(std::string const & binary, std::vector<std::string> & args, std::string const & output, int & pid, bool wait_for_termination)
{
    try {
        boost::process::ipstream pipe_stream;
        boost::filesystem::path bin_url(binary);
        
        if(binary.find("/") == std::string::npos){
            bin_url = boost::process::search_path(binary);
        }

        if(output.empty()){
            boost::process::child bin(bin_url, boost::process::args(args));
            pid = bin.id();         
            
            if(wait_for_termination){
                bin.wait();
                return bin.exit_code();
            } else {
                bin.detach();
                return 0;
            }
        } else {
            std::ofstream log(output);
            std::string line;
            boost::process::child bin(bin_url, boost::process::args(args), boost::process::std_err > pipe_stream);
            pid = bin.id();

            while (pipe_stream && std::getline(pipe_stream, line) && !line.empty()){
                log << line << std::endl;
            }

            if(wait_for_termination){
                bin.wait();
                return bin.exit_code();
            } else {
                bin.detach();
            }
    
            log.close();
            
            return 0;
        }

    } catch (boost::process::process_error const & exp){
        throw YassiException(exp.what());
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}
