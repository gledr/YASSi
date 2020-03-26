#include "yassi_logger.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


Logger* Logger::p_instance = nullptr;
bool Logger::p_singleton = false;

Logger* Logger::getInstance()
{
    if(Logger::p_singleton == false){
        Logger::p_instance = new Logger();
        Logger::p_singleton = true;
    }
    
    return p_instance;;
}

void Logger::destroy()
{
    delete Logger::p_instance;
    Logger::p_instance = nullptr;
    Logger::p_singleton = false;
}

Logger::Logger():
    Object(), BaseLogger()
{
    p_log_stream->set_dump_to_shell(true);
    
    if(this->get_log_file_enabled()){
        p_log_stream->set_dump_to_file(true);
    }    
    if(this->get_quiet()){
        p_log_stream->set_enabled(false);
    } else {
        p_log_stream->set_enabled(true);
    }
    
    p_log_stream->set_working_directory(this->get_execution_url());
    p_log_stream->set_file_name(this->get_logfile_name());
}

Logger::~Logger()
{
    Logger::p_singleton= false;
    delete Logger::p_instance; Logger::p_instance = nullptr;
}

void Logger::generate_bitcode(std::string const & file)
{
    std::stringstream msg;
    msg << "Compiling LLVM IR for Source File: " << file;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::instrument_file_symbolic(std::string const & file)
{
    std::stringstream msg;
    msg << "Running Symbolic Backend IR Instrumentation for Source File: " << file;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}
 
void Logger::link_symbolic_backend(std::string const & bin_name)
{
    std::stringstream msg;
    msg << "Linking Symbolic Backend Binary File: " << bin_name;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::start_symbolic_backend(std::string const & name)
{
    std::stringstream msg;
    msg << "Spawning Symbolic Backend Binary: " << name;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::symbolic_backend_terminated()
{
    std::stringstream msg;
    msg << "Symbolic Backend Binary Terminated!";
    LOG(eInfo)  << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::check_gold_result()
{
    std::stringstream msg;
    msg << "Comparing Generated Results with Gold Model...";
    LOG(eInfo)  << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::check_result_success()
{
    std::stringstream msg;
    msg << "Test Case Success :)";
    LOG(eInfo) << BaseUtils::get_bash_string_green(msg.str());
}

void Logger::check_result_fail()
{
    std::stringstream msg;
    msg << "Test Case Failed :(";
    LOG(eInfo) << BaseUtils::get_bash_string_red(msg.str());
}

void Logger::check_result_unknown()
{
    std::stringstream msg;
    msg << "Test Case Unknown";
    LOG(eInfo) << BaseUtils::get_bash_string_orange(msg.str());
}

void Logger::instrument_file_debug(std::string const & file)
{
    std::stringstream msg;
    msg << "Running Debug Backend IR Instrumentation for Source File: " << file;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::link_debug_backend(std::string const & bin_name)
{
    std::stringstream msg;
    msg << "Linking Debug Backend Binary File: " << bin_name;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::start_debug_backend(std::string const & name)
{
    std::stringstream msg;
    msg << "Spawning Debug Backend Binary: " << name;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::debug_backend_terminated()
{
    std::stringstream msg;
    msg << "Debug Backend Binary Terminated!";
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::instrument_file_replay(const std::string& file)
{
    std::stringstream msg;
    msg << "Running Replay Backend IR Instrumentation for Source File: " << file;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::link_replay_backend(const std::string& bin_name)
{
    std::stringstream msg;
    msg << "Linking Replay Backend Binary File: " << bin_name;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::replay_backend_termianted()
{
    std::stringstream msg;
    msg << "Replay Backend Binary Terminated!";
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::start_replay_backend(const std::string& name)
{
    std::stringstream msg;
    msg << "Spawning Replay Backend Binary: " << name;
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::write_golden_result()
{ 
    std::stringstream msg;
    msg << "Writing Golden Result to Filesystem";
    LOG(eInfo) << BaseUtils::get_bash_string_purple(msg.str());
}

void Logger::cflow_not_found()
{
    LOG(eWarning) << "Cflow missing! Recursions will not be detected...";
}
