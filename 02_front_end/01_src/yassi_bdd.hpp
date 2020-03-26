#ifndef YASSI_BDD_HPP
#define YASSI_BDD_HPP

#include <string>
#include <vector>
#include <algorithm>
#include <map>

#include <boost/filesystem.hpp>

#include <yassi_exception.hpp>
#include <yassi_object.hpp>

namespace Yassi::Frontend {

typedef std::vector<std::string> Path;    

struct PathAndAssign {
    Path path;
    std::string assign;
};

struct Node {
    std::string cond_pos;
    int node_pos;
    int node_neg;
    std::string assign;
};

struct ParentStruct {
	std::string branch;
	int node;
};
    
    
class BDD: public virtual Object {
public:
 
    BDD();
    
    virtual ~BDD();
    
    void show_bdd(std::string title = "");
    void construct_bdd();
    
private:
    
    std::vector<Node> p_nodes;
    
    void make_tree(std::vector<PathAndAssign> paths_and_assign, std::vector<std::string> cond_ordering , int depth = 0);
    
    void part_paths(std::string cond, std::vector<PathAndAssign> input, std::vector<PathAndAssign>& output_pos, std::vector<PathAndAssign>& output_neg );
        
    void get_to_front(std::vector<PathAndAssign>& path_and_assigns, std::string cond_pos, int depth);
    
    std::string negation(std::string cond);
    
    bool contains_pos(Path path, std::string cond);
    
    bool contains_neg(Path path, std::string cond);
    
    std::vector<std::string> remove(std::vector<std::string>input , std::string to_remove);
    
    void add_path(std::vector<Node>& nodes, PathAndAssign path_and_assign, int node_root = 0);
   
    bool is_complete(std::string variable, std::vector<PathAndAssign> table);

    PathAndAssign tail(PathAndAssign path_and_assign);
    
    std::string positive_cond(std::string const & condition);
    
    Path put_nth(std::string cond, Path path, size_t depth);
    
    void print_path_assign(PathAndAssign pa);
    
    /* ROBDD */
    
    void robdd();
    
    void pass_1();
    
    void pass_2();
    
    void pass_3();
    
    void rm_invalid_nodes();
    
    std::vector<ParentStruct> get_parents(int n);

};

}

#endif /* YASSI_BDD_HPP */
