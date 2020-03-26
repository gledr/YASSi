/** 
 * @file yassi_checkmodel.cpp
 * @brief Instrument, Compile and Execute Symbolic Backend Binary
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
#include <yassi_checkmodel.hpp>

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


pid_t   CheckModel::p_pid = 0;
timer_t CheckModel::p_timerid = 0;

/**
 * @brief Constructor
 */
CheckModel::CheckModel():
    Bitcode()
{
    p_timer = new Timer();
    p_checker = new ResultChecker(this->get_execution_url(), this->get_tmp_folder());
}

/**
 * @brief Destructor;
 */
CheckModel::~CheckModel()
{
    delete p_timer;     p_timer = nullptr;
    delete p_checker;   p_checker = nullptr;
}

/**
 * @brief Run Bitcode Instrumentation
 */
void CheckModel::instrument_bitcode()
{
    boost::filesystem::current_path(this->get_src_dir());

    for(auto& file: this->get_source_files()){
        if(Utils::is_source(file) || Utils::is_bc(file)){
            std::string filename = Utils::get_filename(file);
            p_database->insert_build(filename);

            /**
             * First Optimization Pass Stage
             * Use LLVM Default Optmimizations
             */
            std::vector<std::string> cmd_args;
            cmd_args.push_back("-simplifycfg");
            cmd_args.push_back("-reg2mem");
            cmd_args.push_back(this->make_first_ll(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_second_bc(filename));

            int first_pass_ret_val = p_common->system_execute(this->get_opt(), cmd_args, this->get_log_dir() + "/first_opt_pass.log", true);
            
            if(first_pass_ret_val == -1){
                throw YassiException("Can not apply first optimization pass stage! See logfile!");
            }

            if(!boost::filesystem::exists(this->get_src_dir() + this->make_second_bc(filename))){
                throw YassiException("Can not find Bitcode after First Instrumentation!");
            }

            /*
             * Secton Optimization Pass Stage
             * Pre Process the Bitcode using Custom Optimization Pass
             */
            cmd_args.clear();
            cmd_args.push_back("-load");
            cmd_args.push_back(this->get_base_path() + "09_lib/YassiInstr.so");
            if(this->has_seed_function()){
                cmd_args.push_back("-instr_isolate_seed");
                p_database->insert_option("isolate_function", this->get_isolate_function());
            }
            cmd_args.push_back("-instr_demangle_functions");
            cmd_args.push_back(this->make_second_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_third_bc(filename));
            
            int second_pass_ret_val = p_common->system_execute(this->get_opt(), cmd_args, this->get_log_dir() + "/second_opt_pass.log", true);

            if(second_pass_ret_val == -1){
                throw YassiException("Can not apply second optimization pass stage! See logfile!");
            }

            if(!boost::filesystem::exists(this->get_src_dir() + this->make_third_bc(filename))){
                throw YassiException("Can not find Bitcode after Second Instrumentation!");
            }

            /*
             * Third Optimization Pass Stage
             * Run Code Instrumentation for Symbolic Execution 
             */
            cmd_args.clear();
            cmd_args.push_back("-load");
            cmd_args.push_back(this->get_base_path() + "09_lib/YassiInstr.so");
            cmd_args.push_back("-instr_check_model");
            cmd_args.push_back(this->make_third_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_fourth_bc(filename));
            
            int third_pass_ret_val = p_common->system_execute(this->get_opt(), cmd_args, this->get_log_dir() + "/third_opt_pass.log", true);

            if(third_pass_ret_val == -1){
                throw YassiException("Can not apply third optimization pass stage! See logfile!");
            }

            if(!boost::filesystem::exists(this->get_src_dir() + this->make_fourth_bc(filename))){
                throw YassiException("Can not find Bitcode after Third Instrumentation!");
            }
        }
        p_logger->instrument_file_symbolic(file);
    }
}

/**
 * @brief Link Instrumented Test Code with the Backend Library
 */
void CheckModel::link_backend_binary()
{
    boost::filesystem::create_directory(this->get_bin_dir());

    std::string output_file = this->get_bin_dir() + this->get_modelcheck_backend_name();
    std::vector<std::string> obj_files;
    std::vector<std::string> cmd_args;

    boost::filesystem::current_path(this->get_src_dir());  

    for(auto file : this->get_source_files()){
        if(Utils::is_source(file) || Utils::is_bc(file)){
            cmd_args.clear();
            std::string filename = Utils::get_filename(file);

            obj_files.push_back(this->make_fourth_obj(filename));
            cmd_args.push_back("-c");
            cmd_args.push_back(this->make_fourth_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_fourth_obj(filename));

            p_common->system_execute(this->get_cxx(), cmd_args, this->get_log_dir() + "link_objects.txt", true);

            if(!boost::filesystem::exists(this->make_fourth_bc(filename))){
                throw YassiException("Can not find generated Object file!");
            }
        }
    }

    cmd_args.clear();
    cmd_args.push_back("-rdynamic");
    for(auto itor: obj_files){
        cmd_args.push_back(itor);
    }
    cmd_args.push_back(this->get_base_path() + "09_lib/libsymbolic_backend.a");
    cmd_args.push_back(this->get_base_path() + "05_third_party/lib/libsqlite3.a");
    cmd_args.push_back(this->get_base_path() + "05_third_party/lib/libz3.so");
    cmd_args.push_back(this->get_base_path() + "05_third_party/lib/libjsoncpp.a");
    cmd_args.push_back("-lpthread");
    cmd_args.push_back("-ldl");
    cmd_args.push_back("-o");
    cmd_args.push_back(output_file);

    p_common->system_execute(this->get_cxx(), cmd_args, this->get_log_dir() + "link_backend_binary.txt", true);

    if(!boost::filesystem::exists(output_file)){
        throw YassiException("Can not find Backend Binary!");
    }

    p_logger->link_symbolic_backend(this->get_modelcheck_backend_name());
}

/**
 * @brief Timer Handler: Called By Timer to kill Root Backend Pid
 * 
 * @param sig: Signel Id
 * @param si:  Signel Info
 * @param uc: TODO
 */
void CheckModel::timer_handler(int sig, siginfo_t *si, void *uc) 
{
    /*
     * Suppress unused variables warnings by GCC 
     */
    (void) sig;
    (void) si;
    (void) uc;
    
    kill(CheckModel::p_pid, SIGALRM);
    if(timer_delete(CheckModel::p_timerid) != 0){
        perror("Can not disable timer");
    }
}

/**
 * @brief Run the linked backend binary
 */
void CheckModel::execute_backend()
{
    p_database->insert_option("bin_dir", this->get_bin_dir());
    p_database->insert_option("smt_dir", this->get_smt_dir());
    p_database->insert_option("backend_binary", this->get_modelcheck_backend_name());
    p_database->insert_option("max_depth", std::to_string(this->get_max_depth()));
    p_database->insert_option("execution_url", this->get_execution_url());
    p_database->insert_option("dump_memory", this->get_dump_memory() == true ? "true" : "false");

    p_timer->start_timer(eCheckModel);
    p_logger->start_symbolic_backend(this->get_modelcheck_backend_name());
    boost::filesystem::current_path(this->get_bin_dir());

    /**
     * Set LD_LIBRARY_PATH in order to get the correct version of Z3 loaded by the linker
     */
    setenv("LD_LIBRARY_PATH", std::string(this->get_base_path() + "05_third_party/lib").c_str(), 1);
    
    struct sigevent sev;
    struct itimerspec its;
    sigset_t mask;
    struct sigaction sa;

    /* Establish handler for timer signal */
    sa.sa_flags = SA_SIGINFO;
    sa.sa_sigaction = timer_handler;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGUSR1, &sa, nullptr) != 0) {
        perror("Can not set timer handler!");
    }

    /* Block timer signal temporarily */
    sigemptyset(&mask);
    sigaddset(&mask, SIGUSR1);
    if (sigprocmask(SIG_SETMASK, &mask, nullptr) !=  0){
        perror("Can not block timer!");
    }

    /* Create the timer */
    sev.sigev_notify = SIGEV_SIGNAL;
    sev.sigev_signo = SIGUSR1;
    sev.sigev_value.sival_ptr = &CheckModel::p_timerid;
    if (timer_create(CLOCK_REALTIME, &sev, &CheckModel::p_timerid) != 0) {
        perror("Can not create timer!");
    }

    its.it_value.tv_sec = this->get_timeout();
    its.it_value.tv_nsec = 0;
    its.it_interval.tv_sec = 0;
    its.it_interval.tv_nsec = 0;

    if (timer_settime(CheckModel::p_timerid, 0, &its, nullptr) != 0){
        perror("Can not set timer!");
    }

    std::string bin = std::string(this->get_bin_dir() + this->get_modelcheck_backend_name()).c_str();

    if (sigprocmask(SIG_UNBLOCK, &mask, nullptr) != 0) {
        perror("Can not unblock timer!");
    }
    
    std::vector<std::string> cmd_args;
    p_common->system_execute(bin, cmd_args, "", CheckModel::p_pid, true);
  
    p_logger->symbolic_backend_terminated();
    p_timer->end_timer(eCheckModel);

    if(!this->get_quiet()){
        if(p_database->has_results()){
            std::cout << BaseUtils::get_bash_string_cyan("== Yassi has generated results ==") << std::endl;
        }
        if(p_database->has_exceptions()){
            std::cout << BaseUtils::get_bash_string_cyan("== Yassi has generated exceptions ==") << std::endl;
        }
    }
    p_timer->results_to_db();
}

/**
 * @brief Compare the generated results stored in the database with the golden results
 */
void CheckModel::check_results()
{
    if(this->get_quiet()){
        return;
    }

    eCmpStatus result = p_checker->check_results();

    if(result == eSUCCESS){
        p_logger->check_result_success();;
    } else if (result == eFAIL){
        p_logger->check_result_fail();
    } else if (result == eUnknown){
        p_logger->check_result_unknown();
    } else {
        throw YassiException("Unknown CheckResults result obtained!");
    }
}

/**
 * @brief Compare the Bitcode Generated by Clang with the instrumented Bitcode
 */
void CheckModel::compare_bitcode()
{
    std::vector<std::string> cmd_args;
    boost::filesystem::current_path(this->get_src_dir());   
        
    for(auto file : this->get_source_files()){
        if(Utils::is_source(file) || Utils::is_bc(file)){
            std::string filename = Utils::get_filename(file);

            // Disassembly
            cmd_args.clear();
            cmd_args.push_back(this->make_second_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_second_ll(filename));
            p_common->system_execute(this->get_dis_asm() , cmd_args, "", true);

            // Disassembly
            cmd_args.clear();
            cmd_args.push_back(this->make_fourth_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_fourth_ll(filename));
            p_common->system_execute(this->get_dis_asm() , cmd_args, "", true);

            // Kill old Instance of Compare Tool
            cmd_args.clear();
            cmd_args.push_back(this->get_compare_tool());
            p_common->system_execute("pkill", cmd_args, "", true);

            // Comparison
            cmd_args.clear();
            cmd_args.push_back(this->make_second_ll(filename));
            cmd_args.push_back(this->make_fourth_ll(filename));
            p_common->system_execute(this->get_compare_tool(), cmd_args, "", false);
        }
    }
}

/**
 * @brief Show Control Flow Graph
 */
void CheckModel::show_cfg()
{
    if(!boost::filesystem::create_directory(this->get_img_dir())){
        throw YassiException("Could not create Image Directory!");
    }

    std::vector<std::string> cmd_args;
    for(auto& itor : this->get_source_files()){
        std::string filename = Utils::get_filename(itor);
        p_database->insert_build(filename);

        cmd_args.clear();
        cmd_args.push_back("-dot-cfg");
        cmd_args.push_back("-o");
        cmd_args.push_back(this->make_third_bc(filename));

        p_common->system_execute(this->get_opt(), cmd_args, "", true);
    }

    this->show_cfg_common();
}

/**
 * @brief Get the current results from the database and store it using json format
 */
void CheckModel::get_gold_result()
{
    p_logger->write_golden_result();
    p_checker->write_golden_results();
}

/**
 * @brief Show the results availible for the current test case
 * 
 * @param source: Results from the database or from the golden results json file
 */
void CheckModel::show_results(eResultsSource const source)
{
    std::vector<SingleResultPair> results;
    std::string header;
    std::string empty_header;
    
    if(source == eResultsSource::eDatabase){
        results = p_database->get_results();
        header = "Generated Results";
        empty_header = "No Results Generated";
    } else if (source == eResultsSource::eGoldenResult){
        results = p_checker->get_golden_results();
        header = "Golden Results";
        empty_header = "No Golden Results Stored!";
    } else {
        throw YassiException("Check Datasource!");
    }

    size_t const char_name = 15;
    size_t const char_hint = 45;
    size_t const max_hint  = 35;
    size_t const char_val  = 15;
    size_t const char_sol  = 5;
    size_t const chars_line= 90;

    if(results.empty()){
        std::string msg  = BaseUtils::get_bash_string_red("== " + empty_header + " ==");
        std::cout << std::string (msg.size() - 9, '-') << std::endl;
        std::cout << msg << std::endl;
        std::cout << std::string (msg.size() - 9, '-') << std::endl;
    } else {
        std::string msg = "== " + header + " ==";
        std::cout << std::string(chars_line, '-') << std::endl;
        std::cout << std::string((chars_line - msg.size())/2, ' ') << BaseUtils::get_bash_string_red(msg) << std::endl;
        std::cout << std::string(chars_line, '-') << std::endl;

        std::cout << std::left << std::setfill(' ') << std::setw(char_name) << "Name" 
                  << std::left << std::setfill(' ') << std::setw(char_hint) << "Hint"
                  << std::left << std::setfill(' ') << std::setw(char_val)  << "Value"
                  << std::left << std::setfill(' ') << std::setw(char_sol)  << "Solution" << std::endl;

        for(auto itor : results){
            if(itor.reg_hint.size() >= char_hint){
                itor.reg_hint = itor.reg_hint.substr(itor.reg_hint.size() - max_hint, itor.reg_hint.size());
                itor.reg_hint = "..." + itor.reg_hint;
            }

            std::cout << std::left << std::setfill(' ') << std::setw(char_name) << itor.reg_name 
                      << std::left << std::setfill(' ') << std::setw(char_hint) << itor.reg_hint 
                      << std::left << std::setfill(' ') << std::setw(char_val)  << itor.reg_val 
                      << std::left << std::setfill(' ') << std::setw(char_sol)  << itor.solution << std::endl;
        }
        std::cout << std::string(chars_line, '-') << std::endl;
    }

    if(source == eDatabase){
        this->show_execution_traces();
    }
}

/**
 * @brief Show the availible excetions for the current test case
 * 
 * @param source: Exceptions from the database or stored from the golden exceptions file
 */
void CheckModel::show_exceptions(eResultsSource const source)
{
    std::vector<SingleException> exceptions;
    std::string header;
    std::string empty_header;

    if(source == eDatabase){
        exceptions = p_database->get_exceptions();
        header = "Detected Exceptions";
        empty_header = "No exceptions detected!";
    } else if (source == eGoldenResult){ 
        exceptions = p_checker->get_golden_exceptions();
        header = "Golden Exceptions";
        empty_header = "No golden Execptions stored!";
    } else {
        throw YassiException("Invalid Source for Exceptions entered!");
    }

    std::vector<size_t> problem_ids;
    size_t const char_name = 15;
    size_t const char_hint = 45;
    size_t const max_hint  = 35;
    size_t const char_val  = 15;
    size_t const char_sol  = 5;
    size_t const chars_line= 90;

    if(exceptions.empty()){
        std::string msg = BaseUtils::get_bash_string_red("== " + empty_header + " ==");
        std::cout << std::string (msg.size(), '-') << std::endl;
        std::cout << msg << std::endl;
        std::cout << std::string (msg.size(), '-') << std::endl;
    } else {
        std::string msg = "== " + header + " ==";
        std::cout << std::string(chars_line, '-') << std::endl;
        std::cout << std::string((chars_line - msg.size())/2, ' ') << BaseUtils::get_bash_string_red(msg) << std::endl;
        std::cout << std::string(chars_line, '-') << std::endl;
    
        std::cout << std::left << std::setfill(' ') << std::setw(35) << "Exception Type" 
                  << std::left << std::setfill(' ') << std::setw(15) << "Problem ID"
                  << std::left << std::setfill(' ') << std::setw(15) << "Location" 
                  << std::left << std::setfill(' ') << std::setw(15) << "File" << std::endl;
        
        for(auto itor : exceptions){
            problem_ids.push_back(std::stoi(itor.id));
            std::cout << std::left << std::setfill(' ') << std::setw(35) << itor.type
                      << std::left << std::setfill(' ') << std::setw(15) << itor.id
                      << std::left << std::setfill(' ') << std::setw(15) << itor.location
                      << std::left << std::setfill(' ') << std::setw(15) << itor.file << std::endl;
        }
        std::cout << std::string(chars_line, '-') << std::endl;
    }

    if(source == eDatabase){
        std::vector<SingleResultPair> results = p_database->get_results();
        if(!results.empty()){
            std::string msg = "== Error Assignments ==";
            std::cout << std::string(chars_line, '-') << std::endl;
            std::cout << std::string((chars_line - msg.size())/2, ' ') << BaseUtils::get_bash_string_red(msg) << std::endl;
            std::cout << std::string(chars_line, '-') << std::endl;

            std::cout << std::left << std::setfill(' ') << std::setw(char_name) << "Name" 
                    << std::left << std::setfill(' ') << std::setw(char_hint) << "Hint"
                    << std::left << std::setfill(' ') << std::setw(char_val)  << "Value"
                    << std::left << std::setfill(' ') << std::setw(char_sol)  << "Solution" << std::endl;
            
            for(auto itor : results){
                if(std::find(problem_ids.begin(), problem_ids.end(), itor.solution) != problem_ids.end()){
                    if(itor.reg_hint.size() >= char_hint){
                        itor.reg_hint = itor.reg_hint.substr(itor.reg_hint.size() - max_hint, itor.reg_hint.size());
                        itor.reg_hint = "..." + itor.reg_hint;
                    }

                    std::cout << std::left << std::setfill(' ') << std::setw(char_name) << itor.reg_name 
                            << std::left << std::setfill(' ') << std::setw(char_hint) << itor.reg_hint 
                            << std::left << std::setfill(' ') << std::setw(char_val)  << itor.reg_val 
                            << std::left << std::setfill(' ') << std::setw(char_sol)  << itor.solution << std::endl;
                    }
            }
            std::cout << std::string(chars_line, '-') << std::endl;
        }

        std::set<std::string> error_traces = p_database->get_error_traces();
        if(!error_traces.empty()){
            std::string msg = "== Error Traces ==";
            std::cout << std::string(chars_line, '-') << std::endl;
            std::cout << std::string((chars_line - msg.size())/2, ' ') << BaseUtils::get_bash_string_red(msg) << std::endl;
            std::cout << std::string(chars_line, '-') << std::endl;

            for(auto itor : error_traces){
                std::vector<std::string> traces = BaseUtils::tokenize(itor, ",");
                std::stringstream path;
                for(size_t i = 0; i < traces.size()-1; ++i){
                    path << traces[i] << " -> ";
                }
                path << traces.back();

                std::cout << std::left << std::setfill(' ') << std::setw(45) << path.str() << std::endl;
            }
            std::cout << std::string(chars_line, '-') << std::endl;
        }
    }
}

/**
 * @brief Show the traces explored by the execution
 */
void CheckModel::show_execution_traces()
{
    std::set<std::pair<std::string, std::string>> traces = p_database->get_execution_traces();

    if(!traces.empty()){
        std::cout << std::string(64, '-') << std::endl;
        std::cout << std::string(17, ' ') << BaseUtils::get_bash_string_red("== Execution Traces ==") << std::endl;
        std::cout << std::string(64, '-') << std::endl;

        for(auto itor : traces){
            std::vector<std::string> traces = BaseUtils::tokenize(itor.first, ",");
            std::stringstream path;
            for(size_t i = 0; i < traces.size()-1; ++i){
                path << traces[i] << " -> ";
            }
            path << traces.back();

            std::cout << std::left << std::setfill(' ') << std::setw(45) << path.str() 
                        << std::endl;
        }
        std::cout << std::string(64, '-') << std::endl;
    }
}

/**
 * @brief Open the instrumented Bitcode using a Texteditor
 */
void CheckModel::show_instr_bitcode()
{
    std::vector<std::string> cmd_args;
    boost::filesystem::current_path(this->get_src_dir());  

    for(auto file : this->get_source_files()){
        if(Utils::is_source(file)){
            std::string filename = Utils::get_filename(file);

            // Disassembly
            cmd_args.clear();
            cmd_args.push_back(this->make_third_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_third_ll(filename));

            p_common->system_execute(this->get_dis_asm(), cmd_args, "", true);

            // Visualize
            cmd_args.clear();
            cmd_args.push_back(this->make_third_ll(filename));

            p_common->system_execute(this->get_editor(), cmd_args, "", false);
        }
    }
}
