#include "yassi_testvectors.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


/**
 * @brief 
 */
TestVectors::TestVectors():
    Object()
{
}

/**
 * @brief
 */
TestVectors::~TestVectors()
{
}

std::set<std::vector<std::string>> TestVectors::get_test_vectors()
{
    p_variables = p_database->get_test_vector_variables();
    p_results = p_database->get_results();

    std::set<std::string> names;
    std::map<int, std::map<std::string, std::string>> values;

    for(auto itor : p_results){
        names.insert(itor.reg_name);
        values[itor.solution][itor.reg_name] = itor.reg_val;
    }
    return pivot(values, names);
}

void TestVectors::set_vector_of_test_vectors()
{
    p_variables = p_database->get_test_vector_variables();
    p_test_vectors = this->get_test_vectors();
       
    int id = 0;
    int pos = 0;
    for(auto it : p_test_vectors){
        for(auto it2: it){
            TestVector vec;
            vec.variable_name = p_variables[pos].name;
            vec.variable_hint = p_variables[pos].position;
            vec.value = it2;
            vec.vector_id = std::to_string(id);
            pos++;
            pos = pos % p_variables.size();
            p_minimal_test_vectors.push_back(vec);
        }
        id++;
    }
}

std::vector<std::string> TestVectors::covers(std::vector<std::string> const & v1, std::vector<std::string> const & v2)
{
    std::vector<std::string> ret;
    
    for (size_t i = 0; i < v1.size(); i++) {
        if( v1[i] == "X" ){
            ret.push_back( v2[i] );
        } else if( v2[i] == "X" ){
            ret.push_back( v1[i] );
        } else {
            if( v1[i] != v2[i] ){printf("ERROR\n"); exit(0);}
            ret.push_back( v1[i] );
        }
    }
    return ret;
}

bool TestVectors::dontcares(std::vector<std::string> const & v)
{
    for(auto& it : v){
        if(it == "X")
            return true;
    }
    return false;
}

bool TestVectors::covers_bool(std::vector<std::string> const & v1, std::vector<std::string> const & v2)
{
    for (size_t i = 0; i < v1.size(); i++) {
        if( v1[i] != v2[i] && v1[i] != "X" && v2[i] != "X" ){
            return false;
        }
    }
    return true;
}

std::set<std::vector<std::string>> TestVectors::pivot(std::map<int, std::map<std::string, std::string>> & values, std::set<std::string> & names)
{
    // Change "" to X
    for(auto& it : values){
        for(auto& name : names){
            if( it.second[name] == "" ) it.second[name] = "X";
        }
    }

    // Transform to a set of vectors
    std::set<std::vector<std::string>> values_set;
    for(auto& it : values){
        std::vector<std::string> insert_vec;
        for(auto& name : names){
            insert_vec.push_back(it.second[name].c_str() );
        }
        values_set.insert(insert_vec);
    }
	
    // Delete tests that are covered by another
    while(true){
        int prev_size = values_set.size();
        
        std::set<std::vector<std::string>> to_insert;
        std::set<std::vector<std::string>> to_remove;

        for(auto& v1 : values_set){
            for(auto& v2 : values_set){
                if( v1 == v2 ) continue;

                if(!dontcares(v1) ){
                    to_insert.insert(v1);
                }

                if( dontcares(v1) || dontcares(v2) ){
                    if( covers_bool(v1, v2) ){
                        to_remove.insert(v1);
                        to_remove.insert(v2);
                        to_insert.insert( covers(v1, v2) );
                    }
                }
            }
        }
        for(auto& it : to_remove){
            values_set.erase( values_set.find(it) );
        }

        for(auto& it : to_insert){
            values_set.insert(it);
        }

        int size = values_set.size();

        if( size == prev_size ) break;
    }

    std::set<std::vector<std::string> > values_set2;
    for(auto& it : values_set){
        std::vector<std::string> vect = it;
        std::vector<std::string> vect2;
        for(auto it2 : vect){
            if(it2 == "X")
                vect2.push_back("0");
            else
                vect2.push_back(it2);
        }
        values_set2.insert(vect2);
    }

    return values_set2;
}

/**
 * @brief Show the content of the minimal vectors table
 */ 
void TestVectors::show_test_vectors()
{
    if(p_minimal_test_vectors.empty()){
        std::string msg = BaseUtils::get_bash_string_red("== No Test Vectors Generated! ==");
        std::cout << std::string(msg.size()-9, '-') << std::endl;
        std::cout << msg << std::endl;
        std::cout  << std::string(msg.size()-9, '-') << std::endl;
    } else {
        std::string msg = BaseUtils::get_bash_string_red("== Minimal Test Vectors ==");
        std::cout  << std::string(100, '-') << std::endl;
        std::cout  << std::string((100/2)-(msg.size()/2), ' ') << msg << std::endl;
        std::cout  << std::string(100, '-') << std::endl;
        
        std::cout  << std::left << std::setfill(' ') << std::setw(15) << "Vector ID" 
                   << std::left << std::setfill(' ') << std::setw(40) << "Variable"
                   << std::left << std::setfill(' ') << std::setw(40) << "Name Hint"
                   << std::left << std::setfill(' ') << std::setw(10) << "Value"
                   << std::endl;
        
        for(auto itor : p_minimal_test_vectors){
            std::cout  << std::left << std::setfill(' ') << std::setw(15) << itor.vector_id
                       << std::left << std::setfill(' ') << std::setw(40) << itor.variable_name
                       << std::left << std::setfill(' ') << std::setw(40) << itor.variable_hint
                       << std::left << std::setfill(' ') << std::setw(10) << itor.value
                       << std::endl;
        }
        std::cout << std::string(100, '-') << std::endl;
    }
}

void TestVectors::test_vectors_to_db()
{
    this->p_minimal_test_vectors.clear();
    this->set_vector_of_test_vectors();
    
    for(auto& itor: p_minimal_test_vectors){
        p_database->insert_test_vector(itor);
    }
}
