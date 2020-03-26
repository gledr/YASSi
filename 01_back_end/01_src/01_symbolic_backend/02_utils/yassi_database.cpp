#include "yassi_database.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 * 
 * @param url: The location of the databse file
 */
Database::Database(std::string const & url): 
    BaseDatabase(url)
{
    p_debug = false;
    
    this->open_database();
}

/**
 * @brief Destructor
 */
Database::~Database()
{
    this->close_database();
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
        } else if (p_active_transaction == e_problem_number){
            p_problem_cnt = std::stoi(argv[0]);   
        } else if (p_active_transaction == e_options){
            assertion_check(argc == 2);
            p_options[argv[0]] = argv[1];
        } else if (p_active_transaction == e_internal_functions){
            assertion_check(argc == 1);
            p_internal_functions.insert(argv[0]);
        } else if (p_active_transaction == e_external_functions){
            assertion_check(argc == 1);
            p_external_functions.insert(argv[0]);
        } else if (p_active_transaction == e_timer){
            assertion_check(argc == 2);
            std::pair<std::string, std::string> timer_entry;
            timer_entry.first = argv[0];
            timer_entry.second = argv[1];
            p_times.push_back(timer_entry);
        } else {
            throw YassiException("Transaction does not exist: " + std::to_string(p_active_transaction) + " !");
        }
        return 0;
    }
}

/**
 * @brief
 * 
 * @return std::map< std::string, std::string >
 */
std::map<std::string, std::string> Database::get_options()
{
    std::stringstream query;
    query << "SELECT * FROM options;";
    
    p_active_transaction = e_options;
    this->db_command(query.str());
    p_active_transaction = e_init;
    
    return p_options;
}

/**
 * @brief Is the function non-instrumented (external) or not
 * 
 * @param fn_name: The function to explore
 * @return True if external, false if internal function
 */ 
bool Database::is_external_function(const std::string& fn_name)
{
    if(p_external_functions.empty()) {
        this->update_functions();
    }
    
    return std::find(p_external_functions.begin(), p_external_functions.end(), fn_name) != p_external_functions.end();
}

/**
 * @brief Is the function instrumented (internal) or not
 * 
 * @param fn_name: The function to explore
 * @return True if internal, false if external function
 */ 
bool Database::is_internal_function(const std::string& fn_name)
{
    if(p_internal_functions.empty()){
        this->update_functions();
    }
    
    return p_internal_functions.find(fn_name) != p_internal_functions.end();
}

/**
 * @brief Read the functions table from the database
 */ 
void Database::update_functions()
{
    std::stringstream query;
    query << "SELECT * FROM internal_functions;";
    
    p_internal_functions.clear();
    p_external_functions.clear();
    
    p_active_transaction = e_internal_functions;
    this->db_command(query.str());
    p_active_transaction = e_init;
    
    query.str("");
    query << "SELECT * FROM external_functions;";
    
    p_active_transaction = e_external_functions;
    this->db_command(query.str());
    p_active_transaction = e_init;
    
    for(auto& itor : p_internal_functions) {
        if(p_external_functions.find(itor) != p_external_functions.end()){
            p_external_functions.erase(itor);
        }
    }
}

/**
 * @brief
 * 
 * @return std::vector< std::pair< std::string, std::string > >
 */
std::vector<std::pair<std::string, std::string> > Database::get_timer_results()
{
    std::stringstream query;
    query << "SELECT * FROM timer;";
    
    p_times.clear();
    p_active_transaction = e_timer;
    this->db_command(query.str());
    p_active_transaction = e_init;
    
    return p_times;
}

/*
 * @brief Add a new error-execution trace 
 * TODO Merge both trace tables
 */ 
void Database::insert_error_trace(std::vector<std::string> const & paths)
{
	std::string functions_and_bbs_s;

	for(auto& it : paths){
		functions_and_bbs_s += it + ",";
	}

	std::stringstream action;
	action << "insert into error_trace values ('" << functions_and_bbs_s << "');";

    this->db_command(action.str());
}

/**
 * @brief Store the information of a triggered exception
 * 
 * @param type: Type of the triggered exception
 * @param file: File of the triggered execption
 * @param line: Line of the triggered
 */
void Database::insert_exception(const eException& type, std::string const & file, std::string const & line)
{
    int id = this->get_problem_num();
    std::string exception;
    if (type == e_assertion_fail){
        exception = "assertion_fail";
    } else if (type == e_assertion_pass){
        exception = "assertion_pass";
    } else if (type == e_out_of_bounds){
        exception = "out_of_bounds";
    } else if (type == e_divide_by_zero){
        exception = "division by zero";
    } else if (type == e_rem_zero){
        exception = "remainder_by_zero";
    } else if (type == e_deref_range){
        exception = "huge deref range for pointer";
    } else if (type == e_memory_leak){
        exception = "e_memory_leak";
    } else if (type == e_double_free){
        exception = "double free";
    } else {
        notimplemented_check();
    }

    std::stringstream query;
    query << "INSERT INTO exceptions VALUES (" << std::to_string(id) << ",'" << exception << "'," << std::stoi(line) << ",'" << file << "');";
    this->db_command(query.str());
}

/*
 * @brief Add a new execution trace 
 */ 
void Database::insert_trace(std::vector<std::string> const & paths)
{
    std::string functions_and_bbs_s;
    size_t problem_id = this->get_problem_num();
    
    for(auto it : paths){
        functions_and_bbs_s += it + ",";
    }

    std::stringstream action;
    action << "insert into trace values ('" << functions_and_bbs_s << "'," << std::to_string(problem_id) << ");";
    
    this->db_command(action.str());
}

/**
 * @brief
 * 
 * @param sat:
 * @param path:
 */
void Database::insert_problem(std::string const & sat, std::string const & path)
{
    std::stringstream query;
    query << "INSERT INTO problems (sat, path) VALUES (" << sat << ",'" << path << "');";
    this->db_command(query.str());
}

/**
 * @brief Insert the results for one problem/branch into the database
 * 
 * @param name: The unique variable name
 * @param value: The assigned value from the SMT2 engine
 * @param name_hint: The name hint as used in the C code 
 * @param problem_id: The problem_id number to match with other tables
 */
void Database::insert_result(const std::string& name, const std::string& value, const std::string& name_hint, const std::string& problem_id)
{
    std::stringstream query;
    query << "INSERT INTO results (name, value, name_hint, problem_id) values ('" << name << "','" << value << "','" << name_hint << "'," << problem_id << ");";
    this->db_command(query.str());
}

/**
 * @brief
 * 
 * @param name:
 * @param assignment:
 * @param smt2:
 * @param taken:
 */
void Database::insert_branch(const std::string& name, const std::string& assignment, const std::string& smt2, const std::string& taken)
{
    std::stringstream query; 
    query << "INSERT INTO branches (name, assignment, smt2, taken, problem_id) values ('" << name << "','" << assignment << "','" << smt2 << "'," << taken << ","  <<this->get_problem_num() << ");";
    this->db_command(query.str());
}

/**
 * @brief Count the number of problems existing in the db
 *
 * @return The number of problems as int 
 */ 
int Database::get_problem_num()
{
    std::string query = "select count() from problems;";
    
    this->p_active_transaction = e_problem_number;
    this->db_command(query);
    this->p_active_transaction = e_init;
    
    return p_problem_cnt;
}

/**
* @brief Insert a Program Variable into the database
* 
* @param name: The unique name of the variable
* @param name_hint: The name of the variable as used within the program
* @param type: The type of the variable
* @param is_free: Flag if the variable is free/forced free or not
* @param is_unsigned: Flag if the variable is signed or unsigned
*/
void Database::insert_variable(std::string name, std::string const & name_hint, std::string const & type, bool is_free, bool is_unsigned)
{
    std::stringstream action;
    action << "INSERT INTO variables VALUES ('" << name << "','" << name_hint << "','" << type << "'," << std::to_string(is_free)  << "," << std::to_string(is_unsigned) << ") ON CONFLICT(name) DO UPDATE SET name = name;";

    this->db_command(action.str());
}
