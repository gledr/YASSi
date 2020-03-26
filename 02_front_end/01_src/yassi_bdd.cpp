#include "yassi_bdd.hpp"

using namespace Yassi::Frontend;
using namespace Yassi::Utils;


BDD::BDD():
    Object()
{
   
}

BDD::~BDD()
{
    
}

void BDD::construct_bdd()
{
    std::vector<std::string> paths; //   = p_database->get_model_paths();
    std::vector<std::string> assigns; // = p_database->get_model_assigns();
    std::vector<std::string> names;//   = p_database->get_model_names();
    
    //yassi_assertion_check(paths.size() == assigns.size(), __FILE__, __LINE__);
    //yassi_assertion_check(paths.size() == names.size(), __FILE__, __LINE__);
    
    std::vector<PathAndAssign> path_and_assigns;

	for (size_t i = 0; i < paths.size(); i++) {
		PathAndAssign pa;
		pa.path = BaseUtils::tokenize(paths[i], ",");
		pa.assign = assigns[i];
		path_and_assigns.push_back(pa); 
	}
	
	/* Check if there are double negations */
    for(auto& it : path_and_assigns) {
        Path path = it.path;

        for (size_t i = 0; i < path.size(); i++) {
            std::string cond = path[i];

            while(cond.substr(0,10) == "(not (not ") {
                std::string right = cond.substr(10);
                cond = right.substr(0,right.length()-2);
            }
            path[i] = cond;
        }
        it.path = path;
    }
    
    std::set<std::string> variables_set;
	for(auto& it : path_and_assigns){
		Path path = it.path;
		for(auto& it2 : path){
			std::string cond = it2;
			if( cond.substr(0,5) == "(not ")
				variables_set.insert(negation(it2));
			else
				variables_set.insert(it2);
		}
	}
	std::vector<std::string> variables_vec;
    std::copy(variables_set.begin(),variables_set.end(), std::back_inserter(variables_vec));
    
	this->make_tree(path_and_assigns, variables_vec);
	//this->robdd();
}

void BDD::show_bdd(std::string title)
{
    boost::filesystem::create_directory(this->get_img_dir());
      
    std::fstream out_file(this->get_img_dir() + "/digraph.txt", std::ios::out);

    out_file << "digraph G{" << std::endl;
    int i = 0;
    for (auto& node : p_nodes) {
        if(node.node_pos != -1 ){
            out_file << i << " -> " << node.node_pos << " [color=\"green\"]" << std::endl;
        }
        if(node.node_neg != -1 ){
            out_file << i << " -> " << node.node_neg << " [color=\"red\"]" << std::endl;
        }
        i++;
    }

    out_file << "legend_1 [shape=none, margin=0, label=<";
    out_file << "<table border='0' cellborder='0'>";

    if(title != ""){
        out_file << "<tr><td>";
        out_file << title;
        out_file << "</td></tr>" << std::endl;
    }

    for (auto& node : p_nodes) {
        if(node.node_pos == -1 && node.node_neg == -1 && node.assign == "")
            continue;

        std::stringstream row;
        std::string cond_pos = node.cond_pos;
        if(cond_pos == ""){
            cond_pos = "-";
        }
        if(cond_pos.length() > 20){
           // cond_pos = cond_pos.substr(0,20) + "...";
        }

        std::string assign   = node.assign;
        if(assign   == ""){
            assign   = "-";
        }
        if(assign.length()   > 20){
            assign   =   assign.substr(0,20)  + "...";
        }

        row << "<tr>"; 
        row << "<td align='left'>";
        row << i;
        row << "</td>";

        row << "<td align='left'>";
        row << "<font color='green'>" << cond_pos << "</font>";
        row << "</td>";

        row << "<td align='left'>";
        row << "<font color='blue'>" << assign << "</font>";
        row << "</td>";

        row << "</tr>"; 

        out_file << row.str() << std::endl;
    }

    out_file << "</table>";
    out_file << ">];";

    out_file << "}" << std::endl;
    out_file.close();
    
    boost::filesystem::current_path(this->get_img_dir());
    system("dot -T png  digraph.txt > digraph.png");
    system("kde-open digraph.png");
}

void BDD::make_tree(std::vector<PathAndAssign> paths_and_assign, std::vector<std::string> cond_ordering , int depth )
{
	if(paths_and_assign.size() == 1){
		this->add_path(p_nodes, paths_and_assign[0]);
	} else  {
        for(auto it : cond_ordering){
            //printf("variable %s\n", it->c_str());
            if(is_complete(it, paths_and_assign)){
                //printf("is_complete\n");
                std::vector<PathAndAssign> paths_pos;
                std::vector<PathAndAssign> paths_neg;
                this->part_paths(it,paths_and_assign, paths_pos, paths_neg);

                this->get_to_front(paths_pos, it, depth);
                this->get_to_front(paths_neg, it, depth);

                //yassi_assertion_check(paths_pos.size() + paths_neg.size() == paths_and_assign.size(), __FILE__, __LINE__);

                this->make_tree(paths_pos, this->remove(cond_ordering, it) , depth + 1);
                this->make_tree(paths_neg, this->remove(cond_ordering, it) , depth + 1);
            }
        }
    }
}

void BDD::part_paths(std::string cond, std::vector<PathAndAssign> input, std::vector<PathAndAssign>& output_pos, std::vector<PathAndAssign>& output_neg )
{
	for(auto& it : input){
		Path path = it.path;
		if(contains_pos(path, cond) )
			output_pos.push_back(it);
		else if(contains_neg(path, cond))
			output_neg.push_back(it);
		else
            throw YassiException("Malformed BDD");
	}
}

void BDD::get_to_front(std::vector<PathAndAssign> & path_and_assigns, std::string cond_pos, int depth)
{
	for (auto& itor : path_and_assigns) {
          std::cout << "get_to_front" << std::endl;
    
        printf("get_to_front\n---");
        print_path_assign(itor);
        printf("cond_pos %s\n", cond_pos.c_str() );

        Path path = itor.path;
        std::string assign = itor.assign;

        Path path_without_cond;
        std::string cond;

        for(auto it = path.begin(); it != path.end(); it++ ){

            if(cond_pos == *it || cond_pos == negation(*it)){
                cond = *it;
            } else {
                path_without_cond.push_back(*it);
            }
        }

        PathAndAssign path_and_assign_ret;
        path_and_assign_ret.path = put_nth(cond, path_without_cond, depth);
        path_and_assign_ret.assign = assign;

        printf("\n+++");
        print_path_assign(path_and_assign_ret);

        itor = path_and_assign_ret;
	}
}

std::string BDD::negation(std::string cond)
{
	if(cond.substr(0,4) == "(not"){
		std::string right = cond.substr(5);
		std::string center = right.substr(0, right.length()-1);
		return center;
	} else {
		return "(not " + cond + ")";
	}
}

bool BDD::contains_pos(Path path, std::string cond)
{
    std::cout << "contains_pos" << std::endl;
	for(auto& it : path){
		if(cond == it )
			return true;
	}
	return false;
}

bool BDD::contains_neg(Path path, std::string cond)
{
    std::cout << "contains_neg" << std::endl;
	for(auto& it : path){
		if( "(not " + cond + ")" == it)
			return true;
	}
	return false;	
}

void BDD::print_path_assign(PathAndAssign pa)
{
	Path path = pa.path;
	std::string assign = pa.assign;
	for(auto it = path.begin(); it != path.end(); it++ ){
		printf("%s ", it->c_str());
	}
	printf(": %s\n",assign.c_str());
}

std::vector<std::string> BDD::remove(std::vector<std::string> input, std::string to_remove)
{
	std::vector<std::string> ret;
	for(auto it = input.begin(); it != input.end(); it++ ){
		if(*it != to_remove)
			ret.push_back(*it);
	}
	return ret;
}

bool BDD::is_complete(std::string variable, std::vector<PathAndAssign> table)
{
	for(auto it : table){
		PathAndAssign path_and_assign = it;
		Path path = path_and_assign.path;
		bool found = false;
		for(auto it2 : path){
			if(it2 == variable || this->negation(it2) == variable){
				found = true;
            }
		}
		if(!found){
            return false;
        }
	}
	return true;
}

void BDD::add_path(std::vector<Node>& nodes, PathAndAssign path_and_assign, int node_root )
{

	Path path = path_and_assign.path;
	std::string cond = path.size()? path[0]:"";
	std::string assign = path_and_assign.assign;

	if(!nodes.size()){
		Node node = {positive_cond(cond), -1, -1, ""};
		nodes.push_back(node);
		add_path(nodes, path_and_assign, node_root);
	}

	bool follow_pos  = (nodes[node_root].cond_pos == cond && nodes[node_root].node_pos != -1);
	bool follow_neg  = (nodes[node_root].cond_pos == negation(cond) && nodes[node_root].node_neg != -1);
	bool create_pos  = (nodes[node_root].cond_pos == cond && nodes[node_root].node_pos == -1);
	bool create_neg  = (nodes[node_root].cond_pos == negation(cond) && nodes[node_root].node_neg == -1);
	bool is_terminal = (path.size() == 1);

	printf("-----------\n");
	printf("add_path\n");
	print_path_assign(path_and_assign);
	printf("node_root %d\n", node_root);
	printf("cond %s\n", cond.c_str());
	printf("follow_pos %d follow_neg %d create_pos %d create_neg %d is_terminal %d\n", follow_pos, follow_neg, create_pos, create_neg, is_terminal);

	if(follow_pos && !is_terminal){
		add_path(nodes, tail(path_and_assign), nodes[node_root].node_pos );
		return;
	}

	if(follow_neg && !is_terminal){
		add_path(nodes, tail(path_and_assign), nodes[node_root].node_neg);
		return;
	}

	if(create_pos){
		if(is_terminal){
            nodes[node_root].node_pos = nodes.size();
			Node node = { "", -1, -1, assign};
			nodes.push_back(node);
		} else {
            nodes[node_root].node_pos = nodes.size();
			Node node = { positive_cond( path[1] ), -1, -1, ""};
			nodes.push_back(node);
			add_path(nodes, tail(path_and_assign), nodes[node_root].node_pos );
		}
	}

	if(create_neg){
		if(is_terminal){
            nodes[node_root].node_neg = nodes.size();
			Node node = { "", -1, -1, assign};
			nodes.push_back(node);
		} else {
            nodes[node_root].node_neg = nodes.size();
			Node node = {positive_cond( path[1] ), -1, -1, ""};
			nodes.push_back(node);
			add_path(nodes, tail(path_and_assign), nodes[node_root].node_neg );
		}
	}
}

std::string BDD::positive_cond(std::string const & condition)
{
	if(condition.substr(0,5) == "(neg "){
        return negation(condition);
    } else {
        return condition;
    }
}

PathAndAssign BDD::tail(PathAndAssign path_and_assign)
{
	PathAndAssign ret = path_and_assign;
	Path::iterator it_begin = path_and_assign.path.begin() + 1;
	Path::iterator it_end   = path_and_assign.path.end();
	Path retpath = Path(it_begin, it_end);
	ret.path = retpath;

	return ret;
}

Path BDD::put_nth(std::string cond, Path path, size_t depth)
{
	Path ret;

	size_t n = 0;
	for(auto it = path.begin(); it != path.end(); it++,n++ ){
		if(n == depth)
			ret.push_back(cond);
		ret.push_back(*it);
	}

	if(depth == path.size())
		ret.push_back(cond);
	
	return ret;
}

// ROBDD

void BDD::robdd(){
	this->pass_1();
	this->pass_2();
	this->pass_3();
	this->rm_invalid_nodes();
}

void BDD::pass_1()
{
	std::map<std::string, int> map_contents;
	std::set<std::string> set_contents;
	int num_nodes = p_nodes.size();

	for (size_t i = 0; i < p_nodes.size(); i++) {
		if(p_nodes[i].assign != "" && set_contents.find(p_nodes[i].assign) == set_contents.end() ){
			map_contents[p_nodes[i].assign ] = num_nodes;
			set_contents.insert(p_nodes[i].assign);
			num_nodes++;
		}
	}

	for (size_t i = 0; i < p_nodes.size(); i++) {
		if(p_nodes[i].assign != ""){
			std::vector<ParentStruct> parents = get_parents(i);
			int node_dest = map_contents[p_nodes[i].assign ];

			for(auto it = parents.begin(); it != parents.end(); it++ ){
				if(it->branch == "pos"){
					p_nodes[it->node].node_pos = node_dest;
					p_nodes[i].assign = ""; p_nodes[i].node_pos = p_nodes[i].node_neg = -1;
				} else if(it->branch == "neg"){
					p_nodes[it->node].node_neg = node_dest;
					p_nodes[i].assign = ""; p_nodes[i].node_pos = p_nodes[i].node_neg = -1;
				} else if(it->branch == "both"){
					p_nodes[it->node].node_pos = node_dest;
					p_nodes[it->node].node_neg = node_dest;
					p_nodes[i].assign = ""; p_nodes[i].node_pos = p_nodes[i].node_neg = -1;
				}
			}
		}
	}

	for(auto it = set_contents.begin(); it != set_contents.end(); it++ ){
		Node node = { "", -1, -1, *it};
		p_nodes.push_back(node);
	}
}

void BDD::pass_2()
{
	for (size_t i = 0; i < p_nodes.size(); i++) {
		for (size_t k = 0; k < p_nodes.size(); k++) {
			if(p_nodes[i].node_pos == p_nodes[k].node_pos && p_nodes[i].node_neg == p_nodes[k].node_neg){

				if(p_nodes[i].node_pos == -1 && p_nodes[i].node_neg == -1 ) continue;
				if(p_nodes[k].node_pos == -1 && p_nodes[k].node_neg == -1 ) continue;
				if( i == k ) continue;

				std::vector<ParentStruct> parents = get_parents(k);

				for(auto it = parents.begin(); it != parents.end(); it++ ){
					if(it->branch == "pos"){
						p_nodes[it->node].node_pos = i;
						p_nodes[k].assign = ""; p_nodes[k].node_pos = p_nodes[k].node_neg = -1;
					} else if(it->branch == "neg"){
						p_nodes[it->node].node_neg = i;
						p_nodes[k].assign = ""; p_nodes[k].node_pos = p_nodes[k].node_neg = -1;
					} else if(it->branch == "both"){
						p_nodes[it->node].node_pos = i;
						p_nodes[k].assign = ""; p_nodes[k].node_pos = p_nodes[k].node_neg = -1;
					}
				}
			}
		}
	}

	for (size_t i = 0; i < p_nodes.size(); i++) {
		if( (p_nodes[i].node_pos == -1 && p_nodes[i].node_neg == -1) && p_nodes[i].cond_pos != ""){
			std::vector<ParentStruct> parents = get_parents(i);
			for ( unsigned int k = 0; k < parents.size(); k++) {
				int n = parents[k].node;
				p_nodes[n].assign = ""; p_nodes[n].node_pos = p_nodes[n].node_neg = -1;
			}
		}
	}
}

void BDD::pass_3()
{
	for (size_t i = 0; i < p_nodes.size(); i++) {
		if(p_nodes[i].node_pos == p_nodes[i].node_neg ){

			if(p_nodes[i].node_pos == -1) continue;

			std::vector<ParentStruct> parents = get_parents(i);
			int dest = p_nodes[i].node_pos;

			for(auto it = parents.begin(); it != parents.end(); it++ ){
				if(it->branch == "pos"){
					p_nodes[it->node].node_pos = dest;
					p_nodes[i].assign = ""; p_nodes[i].node_pos = p_nodes[i].node_neg = -1;
				} else if(it->branch == "neg"){
					p_nodes[it->node].node_neg = dest;
					p_nodes[i].assign = ""; p_nodes[i].node_pos = p_nodes[i].node_neg = -1;
				} else if(it->branch == "both"){
					p_nodes[it->node].node_pos = dest;
					p_nodes[i].assign = ""; p_nodes[i].node_pos = p_nodes[i].node_neg = -1;
				}
			}
		}
	}
}

void BDD::rm_invalid_nodes()
{
	for (size_t i = 0; i < p_nodes.size(); i++) {
		if(p_nodes[i].node_pos == -1 && p_nodes[i].node_neg == -1 && p_nodes[i].assign == "" ){
			p_nodes.erase(p_nodes.begin() + i);i--;
		}
	}
}

std::vector<ParentStruct> BDD::get_parents(int n)
{
	std::vector<ParentStruct> ret;
	ParentStruct ps;

	for (size_t i = 0; i < p_nodes.size(); i++) {
		if(p_nodes[i].node_pos == n && p_nodes[i].node_neg == n){
			ps.node = i;
			ps.branch = "both";
			ret.push_back(ps);
		} else if(p_nodes[i].node_pos == n){
			ps.node = i;
			ps.branch = "pos";
			ret.push_back(ps);
		} else if(p_nodes[i].node_neg == n){
			ps.node = i;
			ps.branch = "neg";
			ret.push_back(ps);
		}
	}
	return ret;
}
