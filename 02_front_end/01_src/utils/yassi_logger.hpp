#ifndef YASSI_FRONTEND_LOGGER_HPP
#define YASSI_FRONTEND_LOGGER_HPP

#include <yassi_object.hpp>
#include <yassi_baselogger.hpp>

#include <sstream>
#include <chrono>

namespace Yassi::Frontend {
    
class Logger: public virtual Object, public virtual Yassi::Utils::BaseLogger {
public:
    static Logger* getInstance();

   static void destroy();

    void generate_bitcode(std::string const & file);

    void instrument_file_symbolic(std::string const & file);
    void link_symbolic_backend(std::string const & bin_name);
    void start_symbolic_backend(std::string const & name);
    void symbolic_backend_terminated();
    void check_gold_result();
    void check_result_success();
    void check_result_fail();
    void check_result_unknown();
    void write_golden_result();

    void instrument_file_replay(std::string const & file);
    void link_replay_backend(std::string const & bin_name);
    void start_replay_backend(std::string const & name);
    void replay_backend_termianted();

    void instrument_file_debug(std::string const & file);
    void link_debug_backend(std::string const & bin_name);
    void start_debug_backend(std::string const & name);
    void debug_backend_terminated();

    void cflow_not_found();
private:
    Logger();
    virtual ~Logger();

    static Logger* p_instance;
    static bool p_singleton;
};

}

#endif /* YASSI_FRONTEND_LOGGER_HPP */
