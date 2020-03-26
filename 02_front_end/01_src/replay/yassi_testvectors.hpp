#ifndef TESTVECTORS_HPP
#define TESTVECTORS_HPP

#include <vector>
#include <string>
#include <set>
#include <map>
#include <iomanip>

#include <yassi_object.hpp>

namespace Yassi::Frontend {
    
class TestVectors: public virtual Object {
public:
   
    TestVectors();

    ~TestVectors();
    
    void test_vectors_to_db();
    
    void show_test_vectors();
    
private:
    std::set<std::vector<std::string>> p_test_vectors;
    std::vector<Yassi::Utils::TestVector> p_minimal_test_vectors;
    std::vector<Yassi::Utils::SingleResultPair> p_results;
    std::vector<Yassi::Utils::VariableInfo> p_variables;
   
    std::set<std::vector<std::string>> get_test_vectors();
    
    void set_vector_of_test_vectors();
    
    std::vector<std::string> covers(std::vector<std::string> const & v1, std::vector<std::string> const & v2);
    
    bool dontcares(std::vector<std::string> const & v);
    
    bool covers_bool(std::vector<std::string> const & v1, std::vector<std::string> const & v2);
    
    std::set<std::vector<std::string>> pivot(std::map<int, std::map<std::string, std::string>> & values, std::set<std::string> & names);
};

}

#endif /* TESTVECTORS_HPP */
