#ifndef YASSI_REPLAY_DATABASE_HPP
#define YASSI_REPLAY_DATABASE_HPP

#include <map>
#include <set>
#include <sstream>
#include <vector>
#include <string>
#include <algorithm>
#include <iostream>
#include <sqlite3.h>

#include <yassi_baseutils.hpp>
#include <yassi_exception.hpp>
#include <yassi_basedatabase.hpp>
#include <yassi_genericdatastructures.hpp>

namespace Yassi::Backend::Replay {

class Database: public virtual Yassi::Utils::BaseDatabase {
public:
    Database(std::string const & url);
    
    virtual ~Database();

    std::map<std::string, std::string> get_options();
    std::vector<Yassi::Utils::VariableInfo> get_test_vector_variables();
    std::vector<Yassi::Utils::TestVector> get_test_vectors();
    
    std::vector<Yassi::Utils::BasicBlock> get_basic_blocks();
    
    virtual int __callback__(int argc, char **argv, char **azColName);
    
    void insert_measurement(std::string name, std::string value);
    void insert_measurement_trace(std::vector<std::string> const & paths);
    void insert_basic_block(std::string const & file, std::string const & fn, std::string const & bb);
    
private:
    
    enum db_transaction {e_init,
                         e_get_test_vector_variables,
                         e_verbose,
                         e_problem_number,
                         e_get_position,
                         e_results,
                         e_options, 
                         e_test_vectors,
                         e_get_bb
    };
    
    db_transaction p_active_transaction;
    
    std::map<std::string, std::string> p_options;
    std::vector<Yassi::Utils::VariableInfo> p_test_vector_variables;
    std::vector<Yassi::Utils::TestVector> p_test_vectors;
    std::vector<Yassi::Utils::BasicBlock> p_basic_blocks;

    size_t p_problem_cnt;
};

}

#endif /* YASSI_REPLAY_DATABASE_HPP */
