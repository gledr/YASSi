#include "yassi_errorlocalization.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;

ErrorLocalization::ErrorLocalization():
    Bitcode()
{
    p_timer = new Timer();
}

ErrorLocalization::~ErrorLocalization()
{
    delete p_timer;     p_timer = nullptr;
}

void ErrorLocalization::instrument_bitcode()
{
    std::stringstream cmd;
    boost::filesystem::current_path(this->get_src_dir());

    this->write_blacklist();
    
    for (auto file : this->get_source_files()){
        if(Utils::is_source(file)){
            std::string filename = BaseUtils::tokenize(file, ".")[0];

            std::fstream opt_file(this->get_tmp_folder() + "/inprogress.txt", std::ios::out);
            opt_file << filename;
            opt_file.close();

            // First optimization pass
            cmd.str("");
            cmd << this->get_opt() << " -load " << this->get_base_path() << "/09_lib/YassiDebug.so -debug_all < " << filename << ".ll > error_" << filename << "-1.bc";
            system(cmd.str().c_str());

            // Second optimization pass
            cmd.str("");
            cmd << this->get_opt() << " -load " << this->get_base_path() << "/09_lib/YassiInstr.so -reg2mem -instr_check_model < error_" << filename << "-1.bc > error_" << filename << "-2.bc";
            system(cmd.str().c_str());

            cmd.str("");
            cmd << this->get_cxx() << " -c error_" << filename << "-2.bc -o error_" << filename << "-2.o"; 
        
            system(cmd.str().c_str());

            boost::filesystem::remove(this->get_tmp_folder() + "/inprogress.txt");
            
            p_logger->instrument_file_debug(file);
        }
    }
}

void ErrorLocalization::generate_backend_binary()
{
    std::stringstream cmd;
    std::stringstream sources;
    
    boost::filesystem::create_directory(this->get_bin_dir());
    
    for (auto file : this->get_source_files()){
        std::string filename = BaseUtils::tokenize(file, ".")[0];
        sources << "error_" << filename << "-2.o ";
    }
      
    //cmd << this->get_cxx() << " " << sources.str() << " " << this->get_base_path() << "09_lib/libsymbolic_backend.a " << p_config->get_library_search_path() << p_config->get_so_dependencies(eSymbolicBackend) << " -o " <<  this->get_bin_dir() << this->get_bughunter_binary_name();
    system(cmd.str().c_str());
    
    p_logger->link_debug_backend(this->get_bughunter_binary_name());
}

void ErrorLocalization::run_backend_binary()
{
    p_database->insert_option("bin_dir", this->get_bin_dir());
    p_database->insert_option("smt_dir", this->get_smt_dir());
    p_database->insert_option("backend_binary", this->get_modelcheck_backend_name());
    p_database->insert_option("max_depth", std::to_string(this->get_max_depth()));
    p_database->insert_option("error_localization", "true");
    
    boost::filesystem::current_path(this->get_bin_dir());
    
    p_timer->start_timer(eErrorLocal);
    p_logger->start_debug_backend(this->get_bughunter_binary_name());
    system(std::string(this->get_bin_dir() + this->get_bughunter_binary_name()).c_str());
    p_logger->debug_backend_terminated();
    p_timer->end_timer(eErrorLocal);
    p_timer->results_to_db();
}

void ErrorLocalization::write_blacklist()
{
    p_database->create_blacklist_table();
    
    for(auto& itor : this->get_source_files()){
        std::fstream source_file(itor, std::ios::in);
        std::string line;
        size_t line_cnt = 1;
        
        while(std::getline(source_file, line)){
            if(line.find("__VERIFIER_assert") != std::string::npos){
               p_database->insert_blacklist(std::to_string(line_cnt));
            }
            line_cnt++;
        }
    }
}
