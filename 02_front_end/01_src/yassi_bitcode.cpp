/** 
 * @file yassi_bitcode.cpp
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
#include "yassi_bitcode.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 */
Bitcode::Bitcode(): 
    Object(), INTRINSICS_HEADER("#include <yassi.hpp>")
{
    p_logger = Logger::getInstance();
    p_common = new Common();
}

/**
 * @brief Destructor
 */
Bitcode::~Bitcode()
{
    p_logger = nullptr;
    delete p_common;    p_common = nullptr;
}

/**
 * @brief Generate LLVM IR Code for all Source Files
 */
void Bitcode::generate_bitcode()
{
    std::stringstream cmd;
    
    if(this->get_source_files().empty()){
        throw YassiException("No Source Files Provided!");
    }

    this->check_recursive();
    
    if(boost::filesystem::exists(this->get_src_dir() + "/yassi.hpp")){
        boost::filesystem::remove(this->get_src_dir() + "/yassi.hpp");
    }
    
    std::string yassi_include = this->get_base_path() + "01_back_end/02_include/yassi.hpp";
    
    if(!boost::filesystem::exists(yassi_include)){
        throw YassiException("Can not find Yassi Include Header! Are all Paths set correctly?");
    }
    boost::filesystem::copy(yassi_include, this->get_src_dir() + "/yassi.hpp");

    for(auto itor : this->get_source_files()){
        if(!boost::filesystem::exists(itor)){
            throw YassiException("File \"" + itor + "\" does not exist!");
        }
        if(boost::filesystem::exists(this->get_src_dir() + itor)){
            boost::filesystem::remove(this->get_src_dir() + itor);
        }
        boost::filesystem::copy(itor, this->get_src_dir() + itor);

        p_logger->generate_bitcode(itor);
    }

    /*
     * Add the yassi intrinsic header automatically to all source files
     */
    for(auto itor: this->get_source_files()){
        std::ifstream source_file(this->get_src_dir() + itor);
        std::stringstream buffer;
        buffer << source_file.rdbuf();
        source_file.close();

        boost::filesystem::remove(this->get_src_dir() + itor);

        std::ofstream next_file(this->get_src_dir() + itor);
        next_file << INTRINSICS_HEADER << std::endl;
        next_file << std::endl;
        next_file << buffer.str();
        next_file.close();
    }

    std::vector<std::string> cmd_args;
    cmd_args.push_back("-S");
    cmd_args.push_back("-emit-llvm");
    cmd_args.push_back("-g");
    cmd_args.push_back("-O0");
    cmd_args.push_back("-fno-exceptions");

    for(auto itor: this->get_source_files()){
        if(Utils::is_source(itor)){
            cmd_args.push_back(itor);
        }
    }

    cmd_args.push_back("-isystem");
    cmd_args.push_back(this->get_base_path() + "05_third_party/include");
    cmd_args.push_back("-I");
    cmd_args.push_back(this->get_src_dir());
        
    boost::filesystem::current_path(this->get_src_dir());  
    size_t ret_val = p_common->system_execute(this->get_cxx(), cmd_args, this->get_log_dir() + "/compile.log", true);

    if(ret_val != 0){
        throw YassiException("Bitcode Compilation FAILED! See Logfile!");
    }

    for(auto itor: this->get_source_files()){
        if(Utils::is_source(itor)){
            std::string filename = Utils::get_filename(itor);
            if(!boost::filesystem::exists(this->make_first_ll(filename))){
                throw YassiException("Can not find Bitcode file (" + filename + ")");
            }
        }
    }
}

/**
 * @brief Opens the LLVM IR File using the configured text editor
 */
void Bitcode::show_bitcode()
{
    std::vector<std::string> cmd_args;
    boost::filesystem::current_path(this->get_src_dir());  

     for(auto file : this->get_source_files()){
        if(Utils::is_source(file)){
            std::string filename = Utils::get_filename(file);
            p_database->insert_build(filename);

            // First optimization pass
            cmd_args.clear();
            cmd_args.push_back("-load");
            cmd_args.push_back(this->get_base_path() + "09_lib/YassiInstr.so");
            cmd_args.push_back("-instr_fill_names");
            cmd_args.push_back(this->make_first_ll(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_second_bc(filename));

            p_common->system_execute(this->get_opt(), cmd_args, "", true);

            // Disassembly
            cmd_args.clear();
            cmd_args.push_back(this->make_second_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_second_ll(filename));

            p_common->system_execute(this->get_dis_asm(), cmd_args, "", true);

            // Visualize
            cmd_args.clear();
            cmd_args.push_back(this->make_second_ll(filename));

            p_common->system_execute(this->get_editor(), cmd_args, "", false);
        }
    }
}

/**
 * @brief Shows all BasicBlocks
 */
void Bitcode::show_bb()
{
    auto bbs = p_database->get_basic_blocks();

    std::cout << "BasicBlocks: " << bbs.size() <<  std::endl;
    for(auto bb: bbs){
        std::cout << std::get<0>(bb) << " " << std::get<1>(bb) << " " << std::get<2>(bb) << std::endl;;
    }
}

/**
 * @brief Generates the Control Flow Graph from the Sources and shows it using the configured Image Viewer
 */
void Bitcode::show_cfg()
{
    if(!boost::filesystem::create_directory(this->get_img_dir())){
        throw YassiException("Could not create Image Directory!");
    }

    boost::filesystem::current_path(this->get_src_dir());
    std::vector<std::string> cmd_args;

    for(auto& itor : this->get_source_files()){
        std::string filename = Utils::get_filename(itor);
        p_database->insert_build(this->make_first_ll(filename));

        cmd_args.clear();
        cmd_args.push_back("-dot-cfg");
        cmd_args.push_back(this->make_first_ll(filename));
        
        p_common->system_execute(this->get_opt(), cmd_args, "", true);
    }

    this->show_cfg_common();
}

/**
 * @brief Shared Function for generating a png file out of a dot file
 */
void Bitcode::show_cfg_common()
{
    std::vector<std::string> cmd_args; 
    
    for(auto& file: boost::make_iterator_range(boost::filesystem::directory_iterator(this->get_src_dir()), {})){
        if(Utils::is_dot(file.path().string())){
            std::vector<std::string> tokens = BaseUtils::tokenize(file.path().string(), ".");
            assertion_check(tokens.size() == 3);
            boost::filesystem::copy(file.path().string(), this->get_img_dir() + "/cfg." + tokens[1] + "." + tokens[2]);
            boost::filesystem::remove(file.path().string());
        }
    }

    boost::filesystem::current_path(this->get_img_dir());  

    for(auto& file : boost::make_iterator_range(boost::filesystem::directory_iterator(this->get_img_dir()), {})){
        if(Utils::is_dot(file.path().string())){
            std::vector<std::string> tokens = BaseUtils::tokenize(file.path().string(), ".");
            assertion_check(tokens.size() == 3);

            cmd_args.clear();
            cmd_args.push_back("-Tpng");
            cmd_args.push_back(file.path().string());
            cmd_args.push_back("-o");
            cmd_args.push_back(this->get_img_dir() + "/cfg." + tokens[1] + ".png");

            p_common->system_execute("/usr/bin/dot", cmd_args, "", true);
        }
    }

    for(auto& file : boost::make_iterator_range(boost::filesystem::directory_iterator(this->get_img_dir()), {})){
        if(Utils::is_png(file.path().string())){
            cmd_args.clear();
            cmd_args.push_back(file.path().string());

            p_common->system_execute(this->get_image_viewer(), cmd_args, "" ,true);
        }
    }
}

/**
 * @brief Indicates if there are functions used in the code which are not getting instrumented
 */
void Bitcode::list_external_functions() 
{
    boost::filesystem::current_path(this->get_src_dir());  
    std::vector<std::string> cmd_args;
    
    for(auto file : this->get_source_files()){
        std::string filename = Utils::get_filename(file);
        p_database->insert_build(filename);

        cmd_args.clear();
        cmd_args.push_back("-load");
        cmd_args.push_back(this->get_base_path() + "09_lib/YassiInstr.so");
        cmd_args.push_back("-list_external_functions");
        cmd_args.push_back(this->make_first_ll(filename));

        p_common->system_execute(this->get_opt(), cmd_args, "", true);
    }
}

/**
 * @brief Checks if there is a recursion being used in the code using GNU Cflow
 */
void Bitcode::check_recursive()
{
    if(boost::filesystem::exists(boost::process::search_path("cflow"))){

        bool is_recursive = false;

        for(auto& file: this->get_source_files()){

            std::stringstream cmd;
            cmd << "cflow " << file;
            std::array<char, 2500> buffer;
            std::string result;
            std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd.str().c_str(), "r"), pclose);

            nullpointer_check(pipe);

            while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
                result += buffer.data();
            }

            std::smatch match;
            std::regex re("(\\b)*(\\w)*(\\b)*\\(R\\):");
            
            if (std::regex_search(result, match, re) && match.size() > 1) {
            is_recursive = true;
            break;
            }
        }
        p_database->insert_option("recursive", is_recursive ? "true" : "false");
    }
}
