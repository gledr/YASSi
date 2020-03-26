#include "yassi_replay.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 */
Replay::Replay():
    Object()
{
    p_timer = new Timer();
    p_logger = Logger::getInstance();
    p_common = new Common();
}

/**
 * @brief Destructor
 */ 
Replay::~Replay()
{
    delete p_common;    p_common = nullptr;
    delete p_timer;     p_timer = nullptr;
}

/**
 * @brief Link the Replay Backend Binary
 */
void Replay::generate_replay_binary()
{
    boost::filesystem::create_directory(this->get_bin_dir());
    std::vector<std::string> cmd_args;
    
    p_logger->link_replay_backend(this->get_replay_backend_name());
    
    for(auto file: this->get_source_files()){
        std::string filename = Utils::get_filename(file);
        cmd_args.push_back(this->make_third_obj(filename));
    }
    cmd_args.push_back(this->get_base_path() + "09_lib/libreplay_backend.a");
    cmd_args.push_back(this->get_base_path() + "05_third_party/lib/libsqlite3.a");
    cmd_args.push_back("-lpthread");
    cmd_args.push_back("-ldl");
    cmd_args.push_back("-lrt");
    cmd_args.push_back("-o");
    cmd_args.push_back(this->get_bin_dir() + this->get_replay_backend_name());
    
    p_common->system_execute(this->get_cxx(), cmd_args, this->get_log_dir() + "/link_replay_backend.log", true);
    
    if(!boost::filesystem::exists(this->get_bin_dir() + this->get_replay_backend_name())){
        throw YassiException("Can not find Replay Backend!");
    }
}

/**
 * @brief Execute the Replay Backend Binary
 */
void Replay::run_replay()
{
    p_database->insert_option("replay", "true");
    std::vector<std::string> cmd_args;
    boost::filesystem::current_path(this->get_bin_dir());
    
    p_logger->start_replay_backend(this->get_replay_backend_name());
    p_timer->start_timer(eReplay);
    p_common->system_execute(this->get_bin_dir() + "/" + this->get_replay_backend_name(), cmd_args, "", true);
    p_timer->end_timer(eReplay);
    p_logger->replay_backend_termianted();
    p_timer->results_to_db();
}

/**
 * @brief Run Instrumentation Pass and Create Object File
 */
void Replay::instrument_bitcode()
{
    std::vector<std::string> cmd_args;
    boost::filesystem::current_path(this->get_src_dir());

    for (auto file : this->get_source_files()){
        if(Utils::is_source(file)){
            std::string filename = Utils::get_filename(file);
            p_database->insert_build(filename);

            // First optimization pass
            cmd_args.clear();
            cmd_args.push_back("-reg2mem");
            cmd_args.push_back(this->make_first_ll(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_second_bc(filename));
            
            p_common->system_execute(this->get_opt(), cmd_args, this->get_log_dir() + "/replay_first_pass.log", true);
            
            // Second optimization pass
            cmd_args.clear();
            cmd_args.push_back("-load");
            cmd_args.push_back(this->get_base_path() + "/09_lib/YassiReplay.so");
            cmd_args.push_back("-replay_all");
            cmd_args.push_back(this->make_second_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_third_bc(filename));
            
            p_common->system_execute(this->get_opt(), cmd_args, this->get_log_dir() + "/replay_second_pass.log", true);
            
            // Create Object File
            cmd_args.clear();
            cmd_args.push_back("-c");
            cmd_args.push_back(this->make_third_bc(filename));
            cmd_args.push_back("-o");
            cmd_args.push_back(this->make_third_obj(filename));
            
            p_common->system_execute(this->get_cxx(), cmd_args, this->get_log_dir() + "/replay_link_bc.log", true);
            
            p_logger->instrument_file_replay(file);
        }
    }
}

/**
 * @brief Show the Coverage achieved applying the stored test vector
 */
void Replay::show_result()
{
   auto measurements = p_database->get_measurements();
    
    std::cout << std::string(40, '-') << std::endl;
    std::cout << BaseUtils::get_bash_string_cyan("== Stimuli Driven Coverage ==") << std::endl;
    std::cout << std::string(40, '-') << std::endl;
    for(auto itor : measurements){
        std::cout << std::left << std::setfill(' ') << std::setw(20) << itor.first << std::left << std::setfill(' ') << std::setw(20) << itor.second << std::endl;
    }
    std::cout << std::string(40, '-') << std::endl;
}

/**
 * @brief Show the BasicBlocks executed when applying the test vectors
 */ 
void Replay::show_bb()
{
    auto bbs = p_database->get_replay_basic_blocks();
    
    std::cout << "Replay BasicBlocks: " << bbs.size() <<  std::endl;
    for(auto bb: bbs){
        std::cout << std::get<0>(bb) << " " << std::get<1>(bb) << " " << std::get<2>(bb) << std::endl;;
    }
}

/**
 * @brief Compare the Instrumented Bitcode for Replay with the Compiler Generated Bitcode
 */ 
void Replay::compare_bitcode()
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
            
            // Comparison
            cmd_args.clear();
            cmd_args.push_back(this->make_first_ll(filename));
            cmd_args.push_back(this->make_third_ll(filename));
            
            p_common->system_execute(this->get_compare_tool(), cmd_args, "", false);
        }
    }
}
