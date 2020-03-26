/** 
 * @file yassi_frontend.cpp
 * @brief Implementation of the Frontend Class
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
#include "yassi_frontend.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
Frontend::Frontend ():
    Object()
{
}

/**
 * @brief Destructor
 */
Frontend::~Frontend()
{
    delete p_options_functions; p_options_functions = nullptr;
    delete p_exec; p_exec = nullptr;
    //Logger::destroy();
}

/**
 * @brief Initalize the Frontend based on the Commandline Arguments and the Configuration Files
 * 
 * @param argc: Commandline Argument Counter
 * @param argv: Commandline Arguments
 */
void Frontend::init_frontend(int argc, char ** argv) 
{
    p_options_functions = new boost::program_options::options_description("Usage: yassi_nextgen [options]");
    this->program_options(argc, argv); 

    if(p_vm.count("file")){
        this->set_source_files(p_vm["file"].as<std::vector<std::string>>());
    }
    if(p_vm.count("editor")){
        this->set_editor(p_vm["editor"].as<std::string>());
    }
    if(p_vm.count("image_viewer")){
        this->set_image_viewer(p_vm["image_viewer"].as<std::string>());
    }
    if(p_vm.count("compare_tool")){
        this->set_compare_tool(p_vm["compare_tool"].as<std::string>());
    }
    if(p_vm.count("tmp_folder")){
        this->set_tmp_folder(p_vm["tmp_folder"].as<std::string>());
    }
    if(p_vm.count("verbose")){
        this->set_debug(true);
    }
    if(p_vm.count("log_file_enabled")){
        this->set_log_file_enabled(true);
    }
    if(p_vm.count("modelcheck_binary")){
        this->set_modelcheck_backend_name(p_vm["modelcheck_binary"].as<std::string>());
    }
    if(p_vm.count("frontend_binary")){
        p_frontend_name = p_vm["frontend_binary"].as<std::string>();
    }
    if(p_vm.count("replay_binary")){
        this->set_replay_backend_name(p_vm["replay_binary"].as<std::string>());
    }
    if(p_vm.count("max_depth")){
        this->set_max_depth(p_vm["max_depth"].as<int>());
    }
    if(p_vm.count("bughunter_binary")){
        this->set_bughunter_binary_name(p_vm["bughunter_binary"].as<std::string>());
    }
    if(p_vm.count("quiet")){
        this->set_quiet(true);
    }
    if(p_vm.count("dump_memory")){
        this->set_dump_memory(true);
    }
    if(p_vm.count("dump_smt")){
        this->set_dump_smt(true);
    }
    if(p_vm.count("timeout")){
        this->set_timeout(p_vm["timeout"].as<size_t>());
    }
    if(p_vm.count("logfile_name")){
        this->set_logfile_name(p_vm["logfile_name"].as<std::string>());
    }
    if(p_vm.count("isolate_function")){
        this->set_isolate_function(p_vm["isolate_function"].as<std::string>());
    }

    p_database = new Database(this->get_db_dir() + "database.db");

    this->set_execution_url(boost::filesystem::current_path().string());

    p_exec = new Executor();
}

/**
 * @brief Execute the Frontend
 */
void Frontend::run_frontend()
{
    if(!this->get_quiet()) {
        std::fstream ascii_art(this->get_base_path() + "/02_front_end/01_src/yassi.ascii");
        std::vector<std::string> image;
        std::string line;
        while(std::getline(ascii_art, line)){
            image.push_back(line);
            std::cout << line << std::endl;
        }
        ascii_art.close();

        std::cout << "Version: " << GIT_HASH << std::endl;
        std::cout << "Editor : " << GIT_NAME << std::endl;
        std::cout << "Date   : " << GIT_DATE << std::endl;
    }

    if(p_vm.count("show_results")){
       p_exec->runTarget(eShowResultsCheckModel);
    } else if (p_vm.count("show_golden_results")){              // Dumps the stored golden results
        p_exec->runTarget(eShowGoldenResults);                  
    } else if (p_vm.count("show_db")){                          // Opens SqliteBrowser and shows the content of the Database
        p_exec->runTarget(eShowDB);
    } else if (p_vm.count("help")){                             // Displays this information
       std::cout << *p_options_functions << std::endl;
    } else if (p_vm.count("bash_completion")) {                 // Generate a Bash Completion Script
        this->bash_completion_script();
    } else if (p_vm.count("final")){                            // Generates final executable code
        p_exec->runTarget(eLinkCheckModelBinary);
    } else if (p_vm.count("compare_bc")){                       // Opens meld comparing the original and instrumented LLVM IR
        p_exec->runTarget(eCompareBC);
    } else if (p_vm.count("compare_replay_bc")){                // Opens meld comparing the original and the replay instrumented LLVM IR
       p_exec->runTarget(eCompareReplayBC);
    } else if (p_vm.count("view_bc")){                          // Shows bc of the code
        p_exec->runTarget(eShowBC);
    } else if (p_vm.count("view_instr_bc")){                    // Shows the instrumented bc of the code
        p_exec->runTarget((eShowInstrBC));
    } else if (p_vm.count("cfg")){                              // Shows cfg of the code
        p_exec->runTarget(eShowCFG);
    } else if (p_vm.count("cfg2")){                             // Shows cfg of instrumented code
        p_exec->runTarget(eShowModelCheckCFG);
    } else if(p_vm.count("show_test_vectors")){                 // Show generated testvectors
       p_exec->runTarget(eShowTestVectors);
    } else if (p_vm.count("show_coverage")){                    // Shows coverage obtained with current test_vectors
        p_exec->runTarget(eShowReplayResult);
    } else if (p_vm.count("show_bb")){                          // Lists all basic blocks
        p_exec->runTarget(eShowBB);
    } else if (p_vm.count("show_replay_bb")){                   // Lists all replayed basic blocs
        p_exec->runTarget(eShowReplayBB);
    } else if (p_vm.count("clean")){                            // Creates and cleans temporal folder
        p_exec->runTarget(eClean);
    } else if (p_vm.count("replay")){                           // Runs the code with current test_vectors
        p_exec->runTarget(eRunReplay);
    } else if (p_vm.count("get_result")){                       // Copies the results into a txt file as reference for further test cases
        p_exec->runTarget(eCheckModelGoldResult);
    } else if (p_vm.count("list_external_functions")){          // Shows external functions not implemented in the BitCode file
        p_exec->runTarget(eListExternalFunctions);
    } else if (p_vm.count("show_exceptions")){                  // Shows exceptions occurred during execution
        p_exec->runTarget(eShowExceptionCheckModel);
    } else if (p_vm.count("show_golden_exceptions")){           // Shows exceptions stored as golden reference
        p_exec->runTarget(eShowGoldenExceptions);
    } else if (p_vm.count("show_bdd")){                         // Creates a Binary Decision Diagram of the Model and plots it
       p_exec->runTarget(eShowBDD);
    } else if (p_vm.count("run")){                              // Run generated executable
        p_exec->runTarget(eRunCheckModelBackend);
    } else if (p_vm.count("memory_check")){                     // Check for possible Memory Leaks
        p_exec->runTarget(eRunMemoryCheck);
    } else if (p_vm.count("debug")){                            // Run the symbolic debug backend
        p_exec->runTarget(eDebugRun);
    } else if (p_vm.count("test")){                             // Run and check results
        p_exec->runTarget(eCheckModelResults);
    } else if (p_vm.count("make_bc")){
        p_exec->runTarget(eInstrumentCheckModel);
    } else {
       // It seems there is nothing to do here
    }
}

/**
 * @brief Configure Boost Program Options
 * 
 * @param argc: Commandline Argument Counter
 * @param argv: Commandline Arguments
 */
void Frontend::program_options(int const argc, char ** argv) 
{
    p_options_functions->add_options()
        ("help",                        "Displays this information.")
        ("bash_completion",             "Generate a Bash Autocompletion Script")
        ("clean_tables",                "Removes and creates database tables.")
        ("final",                       "Generates final executable code.")
        ("compare_bc",                  "Opens meld comparing the original and symbolic execution instrumented LLVM IR.")
        ("compare_replay_bc",           "Opens meld comparing the original and replay instrumented LLVM IR.")
        ("view_bc",                     "Shows bc of the code.")
        ("view_instr_bc",               "Shows instrumented bc of the code")
        ("cfg",                         "Shows cfg of the code.")
        ("cfg2",                        "Shows dfg of instrumented code.")
        ("run",                         "Run generated executable.")
        ("test",                        "Run and check results.")
        ("show_results",                "Lists the results of a previous yassi run.")
        ("show_golden_results",         "Lists the results stored as golden references")
        ("show_test_vectors",           "Show generated testvectors.")
        ("replay",                      "Stimulate the model with the generated stimuli.")
        ("show_coverage",               "Shows coverage obtained with current test_vectors.")
        ("show_bb",                     "Lists the basic blocks")
        ("show_replay_bb",              "Lists the replayed basic blocks")
        ("clean",                       "Creates and cleans temporal folder.")
        ("get_result",                  "Copies result to gold_result.")
        ("list_external_functions",     "Lists the functions that are not implemented.")
        ("show_exceptions",             "Shows exceptions detected in the program under test.")
        ("show_golden_exceptions",      "Shows exceptions stored as golden reference.")
        ("show_bdd",                    "Shows the complete BDD of the program under test.")
        ("show_db",                     "Opens SqliteBrowser and shows the current database content")
        ("make_bc",                     "Instrument the sources.")
        ("debug",                       "Run Symbolic Debugging")
        ("quiet",                       "UnitTest QuietMode")
        ("verbose",                     "Displays a lot of debug information.")
        ("log_file_enabled",            "Dumps the debug information into a file")
        ("dump_memory",                 "Dumps the content of the internal memory into a file.")
        ("dump_smt",                    "Dumps the SMT2 Problems to the HDD")
        ("memory_check",                "Invoke Valdind for Memory Leak check")
        ("timeout",                     boost::program_options::value<size_t>(),                    "Set the maximal execution time for the backend execution in seconds")
        ("max_depth",                   boost::program_options::value<int>(),                       "Configures the maximum depth for bounded model checking.")
        ("file",                        boost::program_options::value<std::vector<std::string>>(),  "Source Files.")
        ("editor",                      boost::program_options::value<std::string>(),               "The used system editor.")
        ("image_viewer",                boost::program_options::value<std::string>(),               "The used system image viewer.")
        ("logfile_name",                boost::program_options::value<std::string>(),               "The name of the produced logfile")
        ("compare_tool",                boost::program_options::value<std::string>(),               "The used system compare tool.")
        ("tmp_folder",                  boost::program_options::value<std::string>(),               "The location used by Yassi for execution.")
        ("llvm_path",                   boost::program_options::value<std::string>(),               "The location of the llvm tools.")
        ("modelcheck_binary",           boost::program_options::value<std::string>(),               "The name of the backend binary.")
        ("bughunter_binary",            boost::program_options::value<std::string>(),               "The name of the bughunter binary.")
        ("frontend_binary",             boost::program_options::value<std::string>(),               "The name of the frontend binary.")
        ("replay_binary",               boost::program_options::value<std::string>(),               "The name of the replay binary.")
        ("isolate_function",            boost::program_options::value<std::string>(),               "Isolate a single Seed Function to execute");

    // Top Level Priority: Command Line:
    boost::program_options::command_line_parser parser(argc, argv);
    parser.options(*p_options_functions).allow_unregistered().style(boost::program_options::command_line_style::default_style | 
                                boost::program_options::command_line_style::allow_slash_for_short);    

    // Second Level Priority: Local Ini File
    boost::program_options::parsed_options parsed_options1 = parser.run();
    boost::program_options::store(parsed_options1, p_vm);

    std::string base_path = BaseUtils::get_base_path();
    this->set_base_path(base_path);
    std::fstream project_ini = std::fstream("config.ini", std::ios::in);
    boost::program_options::store(boost::program_options::parse_config_file(project_ini, *p_options_functions), p_vm);
    project_ini.close();

    // Third Level Priority: Global Ini File
    std::string config_file = base_path + "/07_configuration/yassi_settings.ini";

    std::fstream global_ini = std::fstream(config_file, std::ios::in);
    boost::program_options::store(boost::program_options::parse_config_file(global_ini, *p_options_functions), p_vm);
    global_ini.close();

    boost::program_options::notify(p_vm);
}

/**
 * @brief Generate a Bash Completion Script based on the configured Boost Program Options
 */
void Frontend::bash_completion_script() 
{
    std::stringstream script;

    script << "#! /bin/bash"                        << std::endl;
    script                                          << std::endl;
    script << "#"                                   << std::endl;
    script << "# Howto Z-Shell:"                    << std::endl;
    script << "# $ autoload bashcompinit"           << std::endl;
    script << "# $ bashcompinit"                    << std::endl;
    script << "# $ source *.sh"                     << std::endl;
    script << "# $ complete -F _" << p_frontend_name << "() -o filename " << p_frontend_name << std::endl;
    script << "#"                                   << std::endl;
    script                                          << std::endl;

    script << "_" << p_frontend_name << " ()"       << std::endl;
    script << "{"                                   << std::endl;
    script << "local cur"                           << std::endl;
    script                                          << std::endl;
    script << "\tCOMPREPLY=()"                      << std::endl;
    script << "\tcur=${COMP_WORDS[COMP_CWORD]}"     << std::endl;
    script                                          << std::endl;
    script << "\tcase \"$cur\" in"                  << std::endl;
    script << "\t\t-*)"                             << std::endl;
    script << "\t\tCOMPREPLY=( $( compgen -W ' \\"  << std::endl;

   for(auto itor : p_options_functions->options()){
        script << "\t\t\t--" << itor->long_name() << " \\" << std::endl;
   }

    script << "\t\t\t' -- $cur ) );;" << std::endl;
    script << "\tesac"                << std::endl;
    script                            << std::endl;
    script << "\treturn 0"            << std::endl;
    script << "}"                     << std::endl;
    
    script << std::endl;
    script << "complete -F _yassi_nextgen  yassi_nextgen" << std::endl;
    
   std::string current_path = boost::filesystem::current_path().string();
   std::fstream out_file(current_path + "/bash_completion_script.sh", std::ios::out);
   out_file << script.str();
   out_file.close();
}
