#include "yassi_database.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 * 
 * @param url: Location of the database file
 */
Database::Database(std::string const & url):
    BaseDatabase(url)
{
    p_debug = false;
}

/**
 * @brief Destructor
 */
Database::~Database()
{

}

////////////////////////////////////////////////////////////////////////////
//                  Database Organization
////////////////////////////////////////////////////////////////////////////
/*
 * @brief Sets up a fresh database - cleans old tables and creates empty ones
 */ 
void Database::init_db()
{
    std::stringstream action;

    /*
     * If there is a db existing, drop all tables despite of the options table 
     */
    bool create_options_table = true;
    if(this->file_exists(p_db_url)){
        create_options_table = false;

        action.str("");
        action << "DROP TABLE problems;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE build;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE reproduced_problems;";
        this->db_command(action.str());
        action.str("");
        action << "DROP TABLE exceptions;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE results;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE measurements;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE timer;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE trace;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE error_trace;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE measurement_trace;";
        this->db_command(action.str());

        action.str("");
        action << "DROP TABLE minimal_vectors;";
        this->db_command(action.str());
    }

    action.str("");
    action << "create table problems(";
    action << "problem_id INTEGER PRIMARY KEY AUTOINCREMENT,";
    action << "sat bool,";
    action << "path varchar(50)";
    action << ");";
    this->db_command(action.str());

    action.str("");
    action << "create table build(";
    action << "filename varchar(50)";
    action << ");";
    this->db_command(action.str());

    action.str("");
    action << "create table reproduced_problems(";
    action << "problem_id INTEGER PRIMARY KEY AUTOINCREMENT,";
    action << "path varchar(50)";
    action << ");";
    this->db_command(action.str());

    action.str("");
    action << "create table exceptions(";
    action << "problem_id integer,";
    action << "exception varchar(50),";
    action << "location integer,";
    action << "file varchar(50)";
    action << ");";
    this->db_command(action.str());

    action.str("");
    action << "create table variables(";
    action << "name varchar(50) PRIMARY KEY,";
    action << "name_hint varchar(50),";
    action << "type varchar(50),";
    action << "is_free bool,";
    action << "is_signed bool";
    action << ");";
    this->db_command(action.str());

    action.str("");
    action << "create table results(";
    action << "name varchar(50),";
    action << "value varchar(50),";
    action << "name_hint varchar(50),";
    action << "problem_id INTEGER";
    action << ");";
    this->db_command(action.str());

    action.str("");
    action << "create table measurements(";
    action << "key varchar(50),";
    action << "value varchar(50)";
    action << ");";
    this->db_command(action.str());

    action.str("");
    action << "create table timer(";
    action << "id varchar(50),";
    action << "time_ms float";
    action << ");";
    this->db_command( action.str() );

    action.str("");
    action << "create table trace (";
    action << "trace varchar(50000),";
    action << "problem_id INTEGER";
    action << ");";
    this->db_command( action.str() );

    action.str("");
    action << "create table error_trace (";
    action << "trace varchar(5000)";
    action << ");";
    this->db_command( action.str() );

    action.str("");
    action << "create table measurement_trace (";
    action << "trace varchar(5000)";
    action << ");";
    this->db_command( action.str() );

    action.str("");
    action << "CREATE TABLE branches(";
    action << "name varchar(5000),";
    action << "assignment bool,";
    action << "smt2 varchar(5000),";
    action << "taken bool,";
    action << "problem_id INTEGER";
    action << ");";
    this->db_command(action.str() );

    if(create_options_table){
        action.str("");
        action << "create table options (";
        action << "key varchar(5000),";
        action << "value varchar(5000)";
        action << ");";
        this->db_command(action.str());

        action.str("");
        action << "create table internal_functions (";
        action << "name varchar(50)";
        action << ");";
        this->db_command(action.str());

        action.str("");
        action << "create table external_functions (";
        action << "name varchar(50)";
        action << ");";
        this->db_command(action.str());
    }

    action.str("");
    action << "create table minimal_vectors (";
    action << "vector_id Integer,";
    action << "variable varchar(50),";
    action << "hint varchar(50),";
    action << "value varchar(50)";
    action << ");";
    this->db_command( action.str());

    action.str("");
    action << "create table basic_blocks (";
    action << "file varchar(50),";
    action << "function varchar(50),";
    action << "bb varchar(50)";
    action << ");";
    this->db_command( action.str());

    action.str("");
    action << "create table replay_basic_blocks (";
    action << "file varchar(50),";
    action << "function varchar(50),";
    action << "bb varchar(50)";
    action << ");";
    this->db_command( action.str());
}

/**
 * @brief Callback function used by the Sqlite3 API - has access to the this pointer
 * 
 * The azColName parameter is unused - since the interface is predefined we told GCC 
 * to ignore this.
 */ 
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int Database::__callback__(int argc, char **argv, char **azColName)
{
#pragma GCC diagnostic pop
    if (*argv == nullptr){
        // If the Table is empty we receive a nullptr
        return 0;
    } else {
        if (p_active_transaction == e_init){
            // Chill dude
        } else if (p_active_transaction == e_verbose){
            // Maybe print it to stdout
        } else if (p_active_transaction == e_measurements){
            std::pair<std::string, std::string> entry;
            entry.first = argv[0];
            entry.second = argv[1];
            p_measurements.push_back(entry);
        } else if (p_active_transaction == e_results){
            SingleResultPair result;
            result.reg_name = argv[0];
            result.reg_hint = argv[1];
            result.reg_val = argv[2];
            result.solution = std::stoi(argv[3]);
            p_results.push_back(result);
        } else if (p_active_transaction == e_exceptions) {
            SingleException  single_exception;
            single_exception.type = argv[1];
            single_exception.id = argv[0];
            single_exception.location = argv[2];
            single_exception.file = argv[3];
            p_exceptions.push_back(single_exception);
        } else if (p_active_transaction == e_error_trace){
            p_error_traces.insert(argv[0]);
        } else if (p_active_transaction == e_get_test_vector_variables){
            VariableInfo var;
            var.name = argv[0];
            var.position = argv[1];
            var.type = argv[2];
            var.free = std::stoi(argv[3]);
            p_test_vector_variables.push_back(var);
        } else if (p_active_transaction == e_trace){
            std::pair<std::string, std::string> entry;
            entry.first = argv[0];
            entry.second = argv[1];
            p_traces.insert(entry);
        } else if (p_active_transaction == e_basic_blocks){
            p_basic_blocks.push_back(std::make_tuple(argv[0], argv[1], argv[2]));
        } else if (p_active_transaction == e_replay_basic_blocks){
            p_replay_basic_blocks.insert(std::make_tuple(argv[0], argv[1], argv[2]));
        } else {
            throw YassiException("Transaction does not exist!");
        }
        return 0;
    }
}

/**
 * @brief
 * 
 * @param key
 * @param value
 */
void Database::insert_option(const std::string& key, const std::string& value)
{
    std::stringstream query;
    query << "INSERT INTO options VALUES(\"" << key << "\",\"" << value << "\");";

    this->db_command(query.str());
}

/**
 * @brief
 * 
 * @param filename
 */
void Database::insert_build(std::string const & filename)
{
    std::stringstream query;
    query << "INSERT INTO build VALUES(\"" << filename << "\");";

    this->db_command(query.str());
}

/**
 * @brief
 * 
 * @param v
 */
void Database::insert_test_vector(TestVector const & v)
{
    std::stringstream query;
    query << "INSERT INTO minimal_vectors VALUES(" << v.vector_id << ",\"" << v.variable_name << "\",\"" << v.variable_hint << "\",\"" << v.value << "\");";

    this->db_command(query.str());
}

/**
 * @brief Getter for the generated results
 */ 
std::vector<SingleResultPair> Database::get_results()
{
    this->update_results();
    return p_results;
}

/**
 * @brief Update the local datastructure for generated results
 */ 
void Database::update_results()
{
    std::stringstream query;
    query << "SELECT  name, name_hint, value, problem_id FROM results;";

    p_results.clear();
    p_active_transaction = e_results;
    this->db_command(query.str());
    p_active_transaction = e_init;
}

/**
 * @brief Show if any exceptions has trigger during execution
 * 
 * @return true if exceptions happend, else false
 */ 
bool Database::has_exceptions()
{
    this->update_exceptions();
    return !p_exceptions.empty();
}

/**
 * @brief Show if any results have been generated
 * 
 * @return true if results are available, else false
 */ 
bool Database::has_results()
{
    this->update_results();

    return !p_results.empty();
}

/**
 * @brief Update local datastructure holding results
 */
void Database::update_exceptions()
{
    std::stringstream query;
    query << "SELECT * FROM exceptions;";

    p_exceptions.clear();
    p_active_transaction = e_exceptions;
    this->db_command(query.str());
    p_active_transaction = e_init;
}

/**
 * @brief
 */
void Database::update_error_trace()
{
    std::stringstream query;
    query << "SELECT * FROM error_trace;";
    
    p_error_traces.clear();
    p_active_transaction = e_error_trace;
    this->db_command(query.str());
    p_active_transaction = e_init;
}

/**
 * @brief
 */
void Database::update_trace()
{
    std::stringstream query;
    query << "SELECT * FROM trace;";
    
    p_traces.clear();
    p_active_transaction = e_trace;
    this->db_command(query.str());
    p_active_transaction = e_init;
    
    std::vector<std::pair<std::string, std::string>> tmp_traces;
    for(auto itor : p_traces){
        std::vector<std::string> tokens = BaseUtils::tokenize(itor.first, ",");
        // If we found a total trace and not only a partial trace
        if(tokens.back() == "end_sim"){
            tmp_traces.push_back(std::make_pair(itor.first, itor.second));
        }
    }
    p_traces.clear();

    for(auto itor : tmp_traces){
        p_traces.insert(std::make_pair(itor.first, itor.second));
    }
}

/**
 * @brief
 * 
 * @return std::set< std::pair< std::string, std::string > >
 */
std::set<std::pair<std::string, std::string>> Database::get_execution_traces()
{
    this->update_trace();
    return p_traces;
}

/**
 * @brief
 * 
 * @return std::vector< Yassi::SingleException >
 */
std::vector<SingleException> Database::get_exceptions()
{
    this->update_exceptions();
    return p_exceptions;
}

/**
 * @brief
 * 
 * @return std::set< std::string >
 */
std::set<std::string> Database::get_error_traces()
{
    this->update_error_trace();
    return p_error_traces;
}

/**
 * @brief 
 * 
 * @return std::vector< std::tuple< std::string, std::string, std::string > >
 */
std::vector<std::tuple<std::string, std::string, std::string> > Database::get_basic_blocks()
{
    this->update_basic_blocks();
    return p_basic_blocks;
}

/**
 * @brief
 */
void Database::update_basic_blocks()
{
    p_basic_blocks.clear();
    std::stringstream query;

    p_active_transaction = e_basic_blocks;
    query << "SELECT * FROM basic_blocks;";
    this->db_command(query.str());
    p_active_transaction = e_init;
}

/**
 * @brief
 * 
 * @return std::set< std::tuple< std::string, std::string, std::string > >
 */
std::set<std::tuple<std::string, std::string, std::string> > Database::get_replay_basic_blocks()
{
    this->update_replay_basic_blocks();
    return p_replay_basic_blocks;
}

/**
 * @brief
 */
void Database::update_replay_basic_blocks()
{
    p_replay_basic_blocks.clear();
    std::stringstream query;

    p_active_transaction = e_replay_basic_blocks;
    query << "SELECT * FROM replay_basic_blocks;";
    this->db_command(query.str());
    p_active_transaction = e_init;
}

/**
 * @brief Reads the data from the measurements table and stores it locally
 */ 
void Database::update_measurements()
{
    std::stringstream query;
    query << "SELECT * FROM measurements";

    p_measurements.clear();
    p_active_transaction = e_measurements;
    this->db_command(query.str());
    p_active_transaction = e_init;
}

/**
 * @brief
 * 
 * @return std::vector< std::pair< std::string, std::string > >
 */
std::vector<std::pair<std::string, std::string> > Database::get_measurements()
{
    this->update_measurements();
    return p_measurements;
}

/**
 * @brief Check is a file exists in the filesystem
 * 
 * @param file: The path to the file to check
 * @return If file exists true, else false
 */ 
bool Database::file_exists(const std::string& file)
{
    std::fstream open_file(file, std::ios::in);
    bool result;
    
    if(open_file.is_open()){
        result = true;
    } else {
        result = false;
    }
    open_file.close();
    
    return result;
}

/**
 * @brief
 * 
 * @return std::vector< Yassi::VariableInfo >
 */
std::vector<VariableInfo> Database::get_test_vector_variables()
{
    p_test_vector_variables.clear();
    
    std::stringstream query;
    query << "SELECT * FROM variables WHERE variables.name in(SELECT name FROM results)";

    p_active_transaction = e_get_test_vector_variables;
    this->db_command(query.str());
    p_active_transaction = e_init;
 
    return p_test_vector_variables;
}

/**
 * @brief Create a Table for Blacklist Communication with Opt Pass Replay
 */
void Database::create_blacklist_table()
{
    std::stringstream query;
    query << "CREATE TABLE blacklist (line_num INTEGER);";

    this->db_command(query.str());
}

/**
 * @brief Insert an entry into the blacklist table
 * 
 * The blacklist table is being used in order to avoid influencing 
 * the forcing SMT assertion.
 * 
 * @param line_num p_line_num: The line number of the forcing assertion
 */
void Database::insert_blacklist(std::string const & line_num)
{
    std::stringstream query;
    query << "INSERT INTO blacklist VALUES (" << line_num << ");";

    this->db_command(query.str());
}
