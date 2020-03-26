#ifndef YASSI_BACKEND_DATABASE_HPP
#define YASSI_BACKEND_DATABASE_HPP

#include <map>
#include <set>
#include <sstream>
#include <vector>
#include <string>

#include <yassi_object.hpp>
#include <sqlite3.h>
#include <yassi_utils.hpp>
#include <yassi_basedatabase.hpp>

namespace Yassi::Backend::Execute {

class Database: public virtual Yassi::Utils::BaseDatabase {
public:
    Database(std::string const & url);
    
    virtual ~Database();
    
    virtual int __callback__(int argc, char **argv, char **azColName);
    
    void insert_error_trace(std::vector<std::string> const & paths);
    void insert_exception(eException const & type,
                          std::string const & file,
                          std::string const & line);
    void insert_trace(std::vector<std::string> const & paths);
    void insert_return_to_os(std::string const & value);
    void insert_variable(std::string name,
                         std::string const & name_hint,
                         std::string const & type,
                         bool is_free,
                         bool is_unsigned);
    void insert_problem(std::string const & sat, std::string const & path);
    void insert_result(std::string const & name,
                       std::string const & value,
                       std::string const & name_hint,
                       std::string const & problem_id);
    void insert_branch(std::string const & name,
                       std::string const & assignment,
                       std::string const & smt2,
                       std::string const & taken);

    int get_problem_num();
    std::vector<std::pair<std::string,std::string>> get_timer_results();
    std::map<std::string, std::string> get_options();

    bool is_internal_function(std::string const & fn_name);
    bool is_external_function(std::string const & fn_name);

private:

    enum db_transaction {e_init,                ///<
                         e_verbose,             ///<
                         e_problem_number,      ///<
                         e_options,             ///<
                         e_timer,               ///<
                         e_internal_functions,  ///<
                         e_external_functions   ///<
    };
    db_transaction p_active_transaction;
    
    std::map<std::string, std::string> p_options;
    std::set<std::string> p_internal_functions;
    std::set<std::string> p_external_functions;
    std::vector<std::pair<std::string, std::string>> p_times;
    
    size_t p_problem_cnt;
    
    void update_functions();
};

}

#endif /* YASSI_BACKEND_DATABASE_HPP */
