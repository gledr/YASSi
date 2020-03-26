/** 
 * @file yassi_datastructuretree.cpp
 * @brief DatastructureTree to represent types like Arrays and Structs
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2019 Johannes Kepler University
 * @author Sebastian Pointner
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
#include "yassi_datastructuretree.hpp"

using namespace Yassi::Utils;

/**
 * @brief Constructor
 */
DatastructureTree::DatastructureTree()
{
    p_address = 0;
    p_depth = 0;
    p_root = nullptr;
}

/**
 * @brief Destructor
 */
DatastructureTree::~DatastructureTree()
{

}

/**
 * @brief
 * 
 * @param tree:
 */
void DatastructureTree::read_tree(std::string const & tree)
{
    p_offset_tree_raw = tree;
    this->destroy_tree();

    std::string _tree = tree;
    p_root = new Node(eNode);
    p_root->level = 0;
    p_root->address = 0;
    p_depth = 0;

    this->parse_next_level(p_root, _tree);
}

/**
 * @brief 
 * 
 * @param root:
 * @param tree:
 */
void DatastructureTree::parse_next_level(Node * root, std::string & tree)
{
#ifdef YASSI
    //nullpointer_check(root);
#else 
    assert (root != nullptr);
#endif
    bool debug = false;
    
    tree = tree.substr(1);
    size_t level_end_1 = tree.find_last_of(",");
    size_t level_end_2 = tree.find_last_of(")");

    std::string bytes = tree.substr(level_end_1+1, level_end_2 - level_end_1 - 1);
    root->bytes = std::stoi(bytes);

    tree = tree.substr(0, level_end_1);
  
    
    if(tree[1] != '(') {
        bool has_subtree = false;
        std::string tree2;
        if(tree.find("((") < tree.size()){
            has_subtree = true;
            size_t pos = tree.find("((");
            debug && std::cout << "has subtype @ :" << pos << std::endl;
            tree2 = tree.substr(pos);
            debug && std::cout << tree2 << std::endl;
            tree = tree.substr(0, pos);
            debug && std::cout << tree << std::endl;
        }
        
        std::vector<int> open;
        std::vector<int> close;
        std::vector<int> comma;

        for(size_t i = 0; i < tree.size(); ++i) {
            if(tree[i] == '(') {
                open.push_back(i);
            } else if (tree[i] == ')') {
                close.push_back(i);
            } else if (tree[i] == ',') {
                comma.push_back(i);
            }
        }

        //yassi_assertion_check (open.size() == close.size(), __FILE__, __LINE__);
        //yassi_assertion_check (close.size() == comma.size(), __FILE__, __LINE__);

        p_subtree.push_back(p_address);
        for(size_t i = 0; i < open.size(); ++i) {
            Node* l = new Node(eLeaf);
            debug && std::cout << tree.substr(open[i] + 1, comma[i] - open[i] - 1) << std::endl;
            l->address = std::stoi(tree.substr(open[i] + 1, comma[i] - open[i] - 1));
            debug && std::cout << tree.substr(open[i] + 1, comma[i] - open[i] - 1) << std::endl;
            l->bytes = std::stoi(tree.substr(comma[i] + 1, close[i] - comma[i] - 1));
            p_address = p_address + l->bytes;
            root->entries.push_back(l);
        }
            
        if(has_subtree){
            Node * node = new Node(eNode);
            node->level = root->level + 1;
            node->address = p_address;
            root->entries.push_back(node);
            p_depth = root->level + 1;

            this->parse_next_level(node, tree2);
        }
        
    } else {
        std::vector<size_t> open;
        std::vector<size_t> close;
        open.push_back(0);

        // Find Closing Bracket for first bracket
        size_t depth = 1;
        for(size_t i = 1; i < tree.size(); ++i) {
            if(tree[i] == '(') {
                depth++;
            } else if (tree[i] == ')') {
                depth--;
            }

            if(depth == 0) {
                close.push_back(i);
                if(i < tree.size()-1) {
                    open.push_back(i+1);
                }
            }
        }

        //yassi_assertion_check (open.size() == close.size(), __FILE__, __LINE__);

        for(size_t i = 0; i < open.size(); ++i) {
            std::string subtree = tree.substr(open[i], close[i] - open[i] + 1);

            Node * node = new Node(eNode);
            node->level = root->level + 1;
            p_depth = root->level + 1;
            node->address = p_address;
            root->entries.push_back(node);

            this->parse_next_level(node, subtree);
        }
    }
}

/**
 * @brief
 */
void DatastructureTree::destroy_tree()
{
    p_address = 0;
    p_subtree.clear();
    
    if(p_root != nullptr) {
        this->destroy_node(p_root);
        p_root = nullptr;
    }
}

/**
 * @brief 
 * 
 * @param index:
 * @return size_t
 */
size_t DatastructureTree::get_offset(std::vector<size_t> const & index)
{
    Node* root = p_root;
    size_t offset = 0;
    for(size_t i = 0; i < index.size(); ++i) {
#ifdef YASSI
        //nullpointer_check(root);
#else 
        assert (root != nullptr);
#endif
        size_t idx = index[i];
        if(i == index.size() -1) {
            //yassi_assertion_check (root->entries.size() >= idx, __FILE__, __LINE__);
            Node* tmp = root->entries[idx];
            
            if(tmp->is_leaf()){
                offset = tmp->address;
            } else if (tmp->is_inner_node()){
                offset = tmp->address;
            } else {
#ifdef YASSI
                throw YassiException("Must not happen!");
#else 
                assert (0);
#endif
            }
            
        } else {
            //yassi_assertion_check(root->entries.size() >= idx, __FILE__, __LINE__);
            Node* branch = static_cast<Node*>(root->entries[idx]);
            root = branch;
        }
    }
    return offset;
}

/**
 * @brief Destroy a node of the tree
 * 
 * @param root: The root node to destroy
 */
void DatastructureTree::destroy_node(Node* root)
{
#ifdef YASSI
    //nullpointer_check(root);
#else 
    assert (root != nullptr);
#endif
    bool debug = false;
    
    if(root->is_inner_node()){
        for(auto itor: root->entries){
            destroy_node(itor);
        }
        debug && std::cout << "delete node level: " << root->level << std::endl;
        delete root; root = nullptr;
    } else if (root->is_leaf()){
       debug &&  std::cout << "delete leaf address: " << root->address << std::endl;
        delete root; root = nullptr;
    }
}

/**
 * @brief
 * 
 * @return std::vector< std::pair< size_t, size_t > >
 */
std::vector<std::pair<size_t, size_t> > DatastructureTree::get_alignment()
{
#ifdef YASSI
    //nullpointer_check(p_root);
#else 
    assert (p_root != nullptr);
#endif
    std::vector<std::pair<size_t, size_t>> retval;
    this->get_alignment(p_root, retval);
    
    return retval;
}

/**
 * @brief
 * 
 * @param root:
 * @param values:
 */
void DatastructureTree::get_alignment(Node* root, std::vector<std::pair<size_t, size_t> >& values)
{
#ifdef YASSI
    //nullpointer_check(root);
#else 
    assert (root != nullptr);
#endif
  
    if(root->is_inner_node()){
        for(auto itor: root->entries){
            this->get_alignment(itor, values);
        }
    } else if (root->is_leaf()){
        values.push_back(std::make_pair(root->address, root->bytes));
    } else {
#ifdef YASSI
        throw YassiException("Must not happen!");
#else 
        assert (0);  
#endif
    }
}

/**
 * @brief
 * 
 * @return std::vector< size_t >
 */
std::vector<size_t> DatastructureTree::subtree()
{
    return p_subtree;
}

/**
 * @brief
 * 
 * @param subtree:
 * @return std::pair< size_t, size_t >
 */
std::pair<size_t, size_t> DatastructureTree::decode_subtree(const std::string& subtree)
{
    std::string tree = subtree.substr(1);
    size_t last_comma = subtree.find_last_of(',');
    tree = tree.substr(0, last_comma - 1);
    
    size_t central_comma = tree.find(",");
    std::string addr = tree.substr(1, central_comma - 1);
   
    std::string size = tree.substr(central_comma + 1, tree.size() - central_comma - 2);
   
    return std::make_pair(std::stoi(addr), std::stoi(size));
}
