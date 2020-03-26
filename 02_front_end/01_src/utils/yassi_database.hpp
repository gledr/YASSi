#ifndef YASSI_FRONTEND_DATABASE_HPP
#define YASSI_FRONTEND_DATABASE_HPP

#include <sstream>
#include <iostream>
#include <set>
#include <tuple>
#include <sqlite3.h>

#include <yassi_object.hpp>
#include <yassi_exception.hpp>
#include <yassi_basedatabase.hpp>
#include <yassi_genericdatastructures.hpp>

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

#include <boost/filesystem.hpp>

namespace Yassi::Frontend {

class Database: public virtual Yassi::Utils::BaseDatabase {
public:
    Database(std::string const & url);

    virtual ~Database();

    virtual int __callback__(int argc, char **argv, char **azColName);

    void init_db();
    void insert_option(std::string const & key, std::string const & value);
    void insert_build(std::string const & filename);

    std::vector<Yassi::Utils::SingleResultPair> get_results();
    std::set<std::pair<std::string, std::string>> get_execution_traces();
    std::set<std::string> get_error_traces();
    std::vector<Yassi::Utils::SingleException> get_exceptions();
    std::vector<std::tuple<std::string, std::string, std::string>> get_basic_blocks();
    std::set<std::tuple<std::string, std::string, std::string>> get_replay_basic_blocks();

    std::vector<std::pair<std::string, std::string>> get_measurements();
    std::vector<Yassi::Utils::VariableInfo> get_test_vector_variables();

    void insert_test_vector(Yassi::Utils::TestVector const & v);

    void create_blacklist_table();
    void insert_blacklist(std::string const & line_num);

    bool has_results();
    bool has_exceptions();

private:
    Database (Database const & db);
    Database operator= (Database const & db);
    bool operator== (Database const & db);

    enum db_transaction {
        e_init                      = 0,  ///<
        e_get_test_vector_variables = 1,  ///<
        e_verbose                   = 2,  ///<
        e_get_position              = 3,  ///<
        e_measurements              = 4,  ///<
        e_results                   = 5,  ///<
        e_exceptions                = 6,  ///<
        e_timer                     = 7,  ///<
        e_error_trace               = 8,  ///<
        e_trace                     = 9,  ///<
        e_options                   = 10, ///<
        e_internal_functions        = 11, ///<
        e_external_functions        = 12, ///<
        e_basic_blocks              = 13, ///<
        e_replay_basic_blocks       = 14  ///<
    };

    db_transaction p_active_transaction;
    std::string p_db_url;

    std::vector<Yassi::Utils::SingleResultPair> p_results;
    std::vector<Yassi::Utils::SingleException> p_exceptions;
    std::vector<Yassi::Utils::VariableInfo> p_test_vector_variables;

    std::set<std::pair<std::string, std::string>> p_traces;
    std::set<std::string> p_error_traces;

    std::vector<std::tuple<std::string, std::string, std::string>> p_basic_blocks;
    std::set<std::tuple<std::string, std::string, std::string>> p_replay_basic_blocks;

    std::vector<std::pair<std::string, std::string>> p_measurements;

    void update_results();
    void update_exceptions();
    void update_error_trace();
    void update_trace();
    void update_measurements();

    void update_basic_blocks();
    void update_replay_basic_blocks();

    bool file_exists(std::string const & fileName);

};

}

#endif /* YASSI_FRONTEND_DATABASE_HPP */
