/** 
 * @file yassi_datastructuretree.hpp
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
#ifndef YASSI_DATASTRUCTURETREE_HPP
#define YASSI_DATASTRUCTURETREE_HPP

#include <string>
#include <iostream>
#include <vector>

#ifdef YASSI
#include <yassi_exception.hpp>
#else 
#include <cassert>
#endif

namespace Yassi::Utils {

enum e_id {eLeaf, eNode};
    
/**
 * @class Node
 * @brief Node Type used in DatastructureTree
 */
class Node {
public:
    Node(e_id id){
        ID = id;
    }
    
    bool is_inner_node()
    {
        return ID == eNode;
    }
    
    bool is_leaf()
    {
        return ID == eLeaf;
    }
    
    size_t address;
    size_t bytes;
    size_t level;
    
    std::vector<Node*> entries;
private:
    e_id ID;
};

/**
 * @class DatastructureTree
 * @brief DatastructureTree for Types like Structs
 */
class DatastructureTree {
public:
    DatastructureTree();

    virtual ~DatastructureTree();

    void read_tree(std::string const & tree);

    size_t get_offset(std::vector<size_t> const & index);

    void destroy_tree();
    
    std::vector<std::pair<size_t, size_t>> get_alignment();
    
    std::vector<size_t> subtree();

private:

    void parse_next_level(Node* root, std::string & tree);
    void destroy_node(Node* root);
    void get_alignment(Node* root, std::vector<std::pair<size_t, size_t>> & values);
    std::pair<size_t, size_t> decode_subtree(std::string const & subtree);
    
    std::string p_offset_tree_raw;
    Node* p_root;
    size_t p_address;
    size_t p_depth;
    std::vector<size_t> p_subtree;
    
};

}

#endif /* YASSI_DATASTRUCTURETREE_HPP */
