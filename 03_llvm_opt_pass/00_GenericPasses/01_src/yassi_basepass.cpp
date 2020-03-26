/** 
 * @file yassi_basepass.cpp
 * @brief Base Class for all Optimization Passes
 * 
 * Yassi Implements Symbolic Execution on the LLVM IR and is able
 * to explore designs in C/C++ including Assertion Checking, Test Generation
 *
 * Copyright (C) 2020 Johannes Kepler University
 * @author Sebastian Pointner
 * @author Pablo Gonzales de Aledo
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
#include "yassi_basepass.hpp"

using namespace Yassi::OptPass;
using namespace Yassi::Types;
using namespace Yassi::Utils;


/**
 * @brief Constructor
 */
BasePass::BasePass() 
{
    MANGLING_SEPERATOR = "%";
    VARIABLE_SEPERATOR = ",";
    
    p_db = new Database();
    p_settings = p_db->get_options();

    if(p_settings["verbose"] == "true"){
        p_verbose = true;
    } else {
        p_verbose = false;
    }
    
    if(p_settings["recursive"] == "true"){
        p_recursive = true;
    } else {
        p_recursive = false;
    }

    p_type_factory = new TypeFactory();
    p_tmp_folder = BaseUtils::get_tmp_folder();
    p_current_source_file = p_db->get_current_build_file();
}

/**
 * @brief Destructor
 */
BasePass::~BasePass()
{
    delete p_type_factory;
    delete p_db;
}

/**
 * @brief Make a Global String
 * 
 * @param M     LLVM Module
 * @param name  Variable Name
 * @return llvm::GlobalVariable*
 */
llvm::GlobalVariable* BasePass::make_global_str(llvm::Module& M, std::string const & name) 
{
    uint64_t length = (uint64_t) name.length()+1;
    llvm::ArrayType* ArrayTy_0 = llvm::ArrayType::get(llvm::IntegerType::get(M.getContext(), 8), length );

    llvm::GlobalVariable* gvar_array_a = new llvm::GlobalVariable(/*Module=*/M,
            /*Type=*/ArrayTy_0,
            /*isConstant=*/false,
            /*Linkage=*/llvm::GlobalValue::ExternalLinkage,
            /*Initializer=*/0, // has initializer, specified below
            /*Name=*/p_current_source_file);

    llvm::Constant* const_array_2 = llvm::ConstantDataArray::getString(M.getContext(), name.c_str(), true);

    // Global Variable Definitions
    gvar_array_a->setInitializer(const_array_2);

    return gvar_array_a;
}

/**
 * @brief Make a Global Int
 * 
 * @param M     LLVM Module
 * @param name  Variable Name
 * @param width Bitwidth of te Variable
 * @return llvm::GlobalVariable*
 */
llvm::GlobalVariable* BasePass::make_global_int(llvm::Module& M, std::string const & name, size_t const width)
{
    llvm::Type* type = llvm::IntegerType::get(M.getContext(), width);
    llvm::GlobalVariable* global_var = new llvm::GlobalVariable(M, type, false, llvm::GlobalValue::CommonLinkage, 0, name);
    llvm::ConstantInt* const_zero_init = llvm::ConstantInt::get(M.getContext(), llvm::APInt(width, llvm::StringRef("0"), 10));
    global_var->setInitializer(const_zero_init);

    return global_var;
}

/**
 * @brief Make a Global Float
 * 
 * @param M     LLVM Module
 * @param name  Variable Name
 * @return llvm::GlobalVariable*
 */
llvm::GlobalVariable* BasePass::make_global_float(llvm::Module& M, std::string const & name)
{
    llvm::Type* type = llvm::Type::getFloatTy(M.getContext());
    llvm::GlobalVariable* global_var = new llvm::GlobalVariable(M, type,  false, llvm::GlobalValue::CommonLinkage, 0, name);
    
    llvm::ConstantFP* const_zero_init = llvm::ConstantFP::get(M.getContext(), llvm::APFloat(0.000000e+00f));
    global_var->setInitializer(const_zero_init);
    
    return global_var;
}

/**
 * @brief Create a new global variable of type double 
 * 
 * @param M:    LLVM Module
 * @param name: Variable NAme
 * @return llvm::GlobalVariable*
 */
llvm::GlobalVariable* BasePass::make_global_double(llvm::Module& M, std::string const & name)
{
    llvm::Type* type = llvm::Type::getDoubleTy(M.getContext());
    llvm::GlobalVariable* global_var = new llvm::GlobalVariable(M, type, false, llvm::GlobalValue::CommonLinkage,0, name);

    llvm::ConstantFP* const_zero_init = llvm::ConstantFP::get(M.getContext(), llvm::APFloat(0.000000e+00));
    global_var->setInitializer(const_zero_init);
    
    return global_var;
}

/**
 * @brief
 * 
 * @param M
 * @param global_var
 * @return llvm::Constant*
 */
llvm::Constant* BasePass::pointerToArray(llvm::Module& M, llvm::GlobalVariable* global_var) 
{
    llvm::ConstantInt* const_int64_10 = llvm::ConstantInt::get(M.getContext(), llvm::APInt(64, llvm::StringRef("0"), 10));
    std::vector<llvm::Constant*> const_ptr_9_indices;
    const_ptr_9_indices.push_back(const_int64_10);
    const_ptr_9_indices.push_back(const_int64_10);

    llvm::Constant* const_ptr_9 = llvm::ConstantExpr::getGetElementPtr(NULL, global_var, const_ptr_9_indices);

    return const_ptr_9;
}

/**
 * @brief
 * 
 * @param operand
 * @return std::string
 */
std::string BasePass::operandname(llvm::Value* operand) 
{
    assert(operand != nullptr);
    
    operand->dump();

    BaseType* type = 
        p_type_factory->get_type_by_enum(static_cast<TypeID>(operand->getType()->getTypeID()),
                                         operand->getType()->getPrimitiveSizeInBits());
    
    if(llvm::isa<llvm::ConstantInt>(operand) ){
        llvm::ConstantInt* CI = llvm::dyn_cast<llvm::ConstantInt>(operand);;
        std::string nameop1 = this->make_constant(type->get_type_identifier(),
                                                  std::to_string(CI->getSExtValue()));
        return nameop1;

    } else if(llvm::isa<llvm::ConstantFP>(operand) ){
        llvm::ConstantFP* CF = llvm::dyn_cast<llvm::ConstantFP>(operand);
        return this->make_constant(type->get_type_identifier(), floatvalue(CF));

    } else if (llvm::isa<llvm::ConstantPointerNull>(operand)){
        return this->make_constant(type->get_type_identifier(), "0");

    } else if(llvm::isa<llvm::GlobalVariable>(operand)){
        return this->make_global_name(operand->getName().str());
    } else if(llvm::isa<llvm::Function>(operand)){
        std::string fun_name = this->demangle_fn_name(operand->getName().str());
        return this->make_function_name(fun_name);
    } else {
        if(operand->getName().str().empty()){
            return this->make_constant(VOIDTYPE, "null");
        } else {
            std::string name = operand->getName().str();
            return this->make_register_name(name);
        }
    }
}

/**
 * @brief
 * 
 * @param CF
 * @return std::string
 */
std::string BasePass::floatvalue(llvm::ConstantFP* CF) 
{
    std::stringstream ret_ss;
    ret_ss.setf( std::ios::fixed, std:: ios::floatfield );
    ret_ss.precision(5);

    if(CF->getType()->getTypeID() == 2) {
        ret_ss << CF->getValueAPF().convertToFloat();
    } else {
        ret_ss << CF->getValueAPF().convertToDouble();
    }
    return ret_ss.str();
}

/**
 * @brief
 * 
 * @param t
 * @return std::string
 */
std::string BasePass::get_flattened_types(const llvm::Type* t)
{
    assert (t != nullptr);
    
    std::string types = this->get_flattened_types_recursive(t);

    return types.substr(0, types.size()-1);
}

/**
 * @brief
 * 
 * @param t
 * @return std::string
 */
std::string BasePass::get_flattened_types_recursive(const llvm::Type* t)
{
    assert (t != nullptr);

    std::stringstream ret;
    BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(t->getTypeID()), t->getPrimitiveSizeInBits());
   
    if(type->is_pointer()){
        ret << type->get_type_identifier() << ":";
        llvm::Type * target_type = t->getPointerElementType();
        assert (target_type != nullptr);    
        BaseType* target_type_obj = p_type_factory->get_type_by_enum(static_cast<TypeID>(target_type->getTypeID()), target_type->getPrimitiveSizeInBits());
        assert (target_type_obj != nullptr);
        ret << target_type_obj->get_type_identifier() << ",";
        
        return ret.str();
        
    } else if (type->is_struct()){
        llvm::StructType const* t_struct = llvm::dyn_cast<llvm::StructType>(t);
        assert (t_struct != nullptr);
        size_t numelems = t_struct->getNumElements();

        for (size_t i = 0; i < numelems; i++) {
            ret << get_flattened_types_recursive(t_struct->getElementType(i));
        }
        
        return ret.str();
        
    } else if (type->is_array()){
        llvm::ArrayType const*  t_array = llvm::dyn_cast<llvm::ArrayType>(t);
        llvm::SequentialType const*  t_sequential = llvm::dyn_cast<llvm::SequentialType>(t);
        assert (t_array != nullptr);
        assert (t_sequential != nullptr);
        size_t numelems = t_array->getNumElements();

        for (size_t i = 0; i < numelems; i++) {
            ret<< get_flattened_types_recursive(t_sequential->getElementType());
        }
        
        return ret.str();
    } else {
        BaseType* type_obj = p_type_factory->get_type_by_enum(static_cast<TypeID>(t->getTypeID()), t->getPrimitiveSizeInBits());
        ret << type_obj->get_type_identifier() <<  ",";
        
        return ret.str();
    }
}

/**
 * @brief
 * 
 * @param t
 * @return int
 */
int BasePass::element_size(const llvm::ArrayType* t)
{
    const llvm::Type* last_type;

    while(true){
        if( !t ) break;
        last_type = t;
        t = llvm::dyn_cast<llvm::ArrayType>(t->getElementType());
    };

    last_type = llvm::dyn_cast<llvm::ArrayType>(last_type)->getElementType();

    const llvm::StructType* t_s = llvm::dyn_cast<llvm::StructType>(last_type);

    if (t_s){
        return sizeofstruct(last_type);
    } else {
        TypeID _enum = static_cast<TypeID>(last_type->getTypeID());
        size_t size = last_type->getPrimitiveSizeInBits();
        BaseType* type = p_type_factory->get_type_by_enum(_enum, size);
        return type->get_bytes();
    }
}

/**
 * @brief 
 * 
 * @param t
 * @return std::vector< int >
 */
std::vector<int> BasePass::get_dimensions(const llvm::ArrayType* t)
{
    std::vector<int> dims;
    while(true){
        if( !t ) break;
        dims.push_back(t->getNumElements());
        t = llvm::dyn_cast<llvm::ArrayType>(t->getElementType());
    }
    return dims;
}

/**
 * @brief
 * 
 * @param t
 * @return int
 */
int BasePass::sizeofstruct(const llvm::Type* t){

    int ret = 0;
    const llvm::StructType* t_s = llvm::dyn_cast<llvm::StructType>(t);

    size_t numelems = t_s->getNumElements();

    for (size_t i = 0; i < numelems; i++) {
        ret += get_size( t_s->getElementType(i) );
    }
    return ret;
}

/**
 * @brief
 * 
 * @param t
 * @param base
 * @return std::string
 */
std::string BasePass::get_offset_tree_rec(llvm::Type* t, int & base)
{
    assert (t != nullptr);
    
    BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(t->getTypeID()), t->getPrimitiveSizeInBits());

    if(type->is_pointer() || type->is_real_class() || type->is_integer_class()){
        std::string ret = "(" + std::to_string(base) + "," + std::to_string(this->get_offset(t)) + ")";
        base += type->get_bytes();
        return ret;

    } else if(type->is_struct()){
        llvm::StructType const* t_struct = llvm::dyn_cast<llvm::StructType>(t);
        std::string aux = "(";
        if(t_struct->getNumElements() == 0){
            aux += "0";
        } else {
            for (size_t i = 0; i < t_struct->getNumElements(); i++) {
                aux += get_offset_tree_rec(t_struct->getElementType(i), base);
            }
        }
        aux += ",1";
        aux += ")";
        
        return aux;

    } else if(type->is_array()){
        llvm::ArrayType const* t_array = llvm::dyn_cast<llvm::ArrayType>(t);
        llvm::CompositeType const* t_composite    = llvm::dyn_cast<llvm::CompositeType>(t);
        llvm::CompositeType const* t_composite_2  = llvm::dyn_cast<llvm::CompositeType>(t_composite);
        std::string aux = "(";
        for (size_t i = 0; i < t_array->getNumElements(); i++) {
            aux += this->get_offset_tree_rec(t_composite_2->getTypeAtIndex(i), base);
        }
        aux += "," + std::to_string(this->get_offset(t));
        aux += ")";

        return aux;

    } else {
        std::cerr << "----" << std::endl;
        std::cerr << "otro" << std::endl;
        t->dump();
        std::cerr << type->get_type_identifier() << std::endl;
        assert(0 && "Unknown Type");
    }
}

/**
 * @brief
 * 
 * @param t
 * @return std::string
 */
std::string BasePass::get_offset_tree(llvm::Type* t)
{
    assert(t != nullptr);

    const llvm::SequentialType* t_sequential  = (llvm::SequentialType* )t;
    BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(t->getTypeID()), t->getPrimitiveSizeInBits());

    auto element_type = t_sequential->getElementType();
    assert(t_sequential != nullptr);
    assert(type->is_pointer());

    int base = 0;
    std::string result =  "(" + get_offset_tree_rec(element_type, base) + "," + std::to_string(get_size(element_type)) + ")";
    return result;
}

/**
 * @brief
 * 
 * @param t
 * @return int
 */
int BasePass::get_offset(llvm::Type* t)
{
    assert (t != nullptr);
    BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(t->getTypeID()), t->getPrimitiveSizeInBits());
    assert (type != nullptr);

    if(type->is_integer_class() || type->is_real_class() || type->is_pointer()) {
        return type->get_bytes();
    } else if(type->is_struct()){
        return 1;
    } else if(type->is_array()){
        llvm::ArrayType const* t_array = llvm::dyn_cast<llvm::ArrayType>(t);
        llvm::CompositeType const* t_composite = llvm::dyn_cast<llvm::CompositeType>(t);
        llvm::CompositeType const* t_composite_2  = llvm::dyn_cast<llvm::CompositeType>(t_composite);
        
        int sum = 0;
        for (size_t i = 0; i < t_array->getNumElements(); i++) {
            sum += get_offset(t_composite_2->getTypeAtIndex(i));
        }
        return sum;

    } else {
        std::cerr << type->get_type_identifier() << std::endl;
        assert(0 && "Unknown Type");
    }
}

/**
 * @brief
 * 
 * @param t
 * @return int
 */
int BasePass::get_size(const llvm::Type* t )
{
    const llvm::ArrayType* t_a = llvm:: dyn_cast<llvm::ArrayType>(t);
    const llvm::StructType* t_s = llvm::dyn_cast<llvm::StructType>(t);

    if(t_a){
        return this->product(this->get_dimensions(t_a))*element_size(t_a);
    } else if (t_s){
        return this->sizeofstruct(t);
    } else {
        BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(t->getTypeID()), t->getPrimitiveSizeInBits());
        return type->get_bytes();
    }
}

/**
 * @brief
 * 
 * @param name
 * @return std::string
 */
std::string BasePass::make_register_name(std::string const & name) 
{
    assert (!name.empty());
 
    if(BaseUtils::tokenize(name, MANGLING_SEPERATOR).size() > 1){
        return name;
    } else {
        return "register" + MANGLING_SEPERATOR + name;
    }
}

/**
 * @brief
 * 
 * @param type
 * @param value
 * @return std::string
 */
std::string BasePass::make_constant(std::string const & type, std::string const & value) 
{
    assert (!type.empty());

    if(!value.empty()) {
        return "constant" + MANGLING_SEPERATOR + type + MANGLING_SEPERATOR + value;
    } else {
        return "constant" + MANGLING_SEPERATOR + type;
    }
}

/**
 * @brief
 * 
 * @param name
 * @return std::string
 */
std::string BasePass::make_global_name(const std::string& name) 
{
    assert(!name.empty());

    return "global" + MANGLING_SEPERATOR + name;
}

/**
 * @brief
 * 
 * @param name
 * @return std::string
 */
std::string BasePass::make_function_name(const std::string& name)
{
    assert(!name.empty());

    return"function" + MANGLING_SEPERATOR + name;
}

bool BasePass::is_special_llvm_function(std::string const & fn_name)
{
    if(fn_name.find("llvm.memcpy") != std::string::npos)            return true;
    if(fn_name.find("llvm.dbg.declare") != std::string::npos)       return true;
    if(fn_name.find("__CXX_global_var_init") != std::string::npos)  return true;

    return false;
}

/**
 * @brief
 * 
 * @param fn_name
 * @return bool
 */
bool BasePass::is_internal_yassi_function(const std::string& fn_name)
{
    if(fn_name == BACKEND_METHOD_GLOBAL_INIT) return true;
    
    return false;
}


/**
 * @brief
 * 
 * @param ins
 * @return std::string
 */
std::string BasePass::line_number_of_instruction(llvm::Instruction const & ins)
{
    llvm::DebugLoc debug_infos = ins.getDebugLoc();
    std::string retVal;

    if(debug_infos.get()){
        size_t linenum = debug_infos.getLine();
        retVal = std::to_string(linenum);
    }  else {
        retVal = "-1";
    }
    return this->make_constant(INTEGER32TYPE, retVal);
}

/**
 * @brief
 * 
 * @param elem
 * @return int
 */
int BasePass::product(std::vector<int> elem)
{
    int prod = 1;
    for(auto it = elem.begin(); it != elem.end(); it++ ){
        prod *= *it;
    }
    return prod;
}

/**
 * @brief
 * 
 * @param str
 * @return std::string
 */
std::string BasePass::demangle_fn_name(const std::string& str) 
{
    std::string _unmangled_fn_name = boost::core::demangle(str.c_str());
    std::vector<std::string> token = BaseUtils::tokenize(_unmangled_fn_name, "(");
    return token.front();
}
