/** 
 * @file yassi_globalinit.cpp
 * @brief Optimization Pass to handle global variables
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
#include "yassi_globalinit.hpp"

using namespace Yassi::OptPass::Execute;
using namespace Yassi::Types;
using namespace Yassi::Utils;

char GlobalInitPass::ID = 0;

GlobalInitPass::GlobalInitPass():
    InstrBase(), 
    llvm::ModulePass(GlobalInitPass::ID)
{
    p_type_tree = new Yassi::Utils::DatastructureTree();
}

GlobalInitPass::~GlobalInitPass() 
{
    delete p_type_tree; p_type_tree = nullptr;
}

bool GlobalInitPass::runOnModule(llvm::Module& M) 
{
    if(!M.getFunction("main")) {
        p_verbose && std::cerr << "No Main Function - Nothing to do" << std::endl;
        return false;
    } else  {
        llvm::Function * target_fun = nullptr;
        
        /*
         * If there is already a global init function existing from LLVM we 
         * are going to copy that function and use it, else we have to creat our own
         */ 
        for(auto fun = M.begin(), function_end = M.end(); fun != function_end; ++fun) {
            if(fun->getName().str().find("_GLOBAL") != std::string::npos){
                target_fun = llvm::dyn_cast<llvm::Function>(fun);
                break;
            }
        }
        
        if(target_fun){
            target_fun->setName(BACKEND_METHOD_GLOBAL_INIT);
            target_fun->setLinkage(llvm::GlobalValue::LinkageTypes::ExternalLinkage);
        } else {
            std::vector<llvm::Type*>FuncTy_3_args;
            llvm::FunctionType* func_type = llvm::FunctionType::get(llvm::Type::getVoidTy(M.getContext()), FuncTy_3_args, false);
            target_fun = llvm::Function::Create(func_type, llvm::GlobalValue::ExternalLinkage, BACKEND_METHOD_GLOBAL_INIT, &M);
            llvm::BasicBlock* label_entry = llvm::BasicBlock::Create(M.getContext(), "entry", target_fun, 0);
            llvm::ReturnInst::Create(M.getContext(), nullptr, label_entry);
        }
        
        size_t current_addr = 0;
        // Resolve the position of each global variable in the Yassi Memory
        for(auto gl = M.global_begin(), gl_end = M.global_end();  gl != gl_end; ++gl) {
            std::string name = this->make_global_name(gl->getName().str());
            given_addr[name] = current_addr;
            current_addr++;
        }

        std::vector<VarInit> global_var_inits;
        for(auto gl = M.global_begin(), gl_end = M.global_end();  gl != gl_end; ++gl) {
            const llvm::PointerType* pointertype = llvm::cast<llvm::PointerType>(gl->getType());
            const llvm::Type*        type_t       = pointertype->getElementType();

            llvm::GlobalVariable*    global_var   = llvm::cast<llvm::GlobalVariable>(gl);

            std::string name = this->make_global_name(gl->getName().str());
            std::string types = this->get_flattened_types(type_t);
            std::string vals;
            
            if(gl->hasInitializer()) {
                llvm::Constant* constant = global_var->getInitializer();
                vals = this->get_flattened_vals(constant);
            } else {
                std::vector<std::string> tokens = BaseUtils::tokenize(types, ",");
                for(auto it: tokens) {
                    vals += "X,";
                }
            }

            VarInit varinit = {name, types, vals};
            global_var_inits.push_back(varinit);
        }
        
        llvm::BasicBlock::iterator insertpos = target_fun->begin()->begin();
       
        for(auto it : global_var_inits) {
            llvm::GlobalVariable* c1 = this->make_global_str(M, it.name);
            llvm::GlobalVariable* c2 = this->make_global_str(M, it.type);
            llvm::GlobalVariable* c3 = this->make_global_str(M, it.initialization);

            llvm::FunctionType * gl_init_type = llvm::TypeBuilder<void(char*, char*, char*), false>::get(M.getContext());
            llvm::Function* gl_init_fun = llvm::cast<llvm::Function>(M.getOrInsertFunction(BACKEND_FN_GLOBAL_INIT, gl_init_type));
            
            std::vector<llvm::Value*> params;
            params.push_back(this->pointerToArray(M,c1));
            params.push_back(this->pointerToArray(M,c2));
            params.push_back(this->pointerToArray(M,c3));
            llvm::CallInst::Create(gl_init_fun, params, "", llvm::cast<llvm::Instruction>(insertpos));
        }
        return false;
    }
}

std::string GlobalInitPass::get_flattened_vals(llvm::Constant* constant) 
{
    llvm::ConstantInt*         constant_int          = llvm::dyn_cast<llvm::ConstantInt>(constant);
    llvm::ConstantArray*       constant_array        = llvm::dyn_cast<llvm::ConstantArray>(constant);
    llvm::ConstantDataArray*   constant_data_array   = llvm::dyn_cast<llvm::ConstantDataArray>(constant);
    llvm::ConstantFP*          constant_float        = llvm::dyn_cast<llvm::ConstantFP>(constant);
    llvm::ConstantStruct*      constant_struct       = llvm::dyn_cast<llvm::ConstantStruct>(constant);
    llvm::ConstantPointerNull* constant_pointer_null = llvm::dyn_cast<llvm::ConstantPointerNull>(constant);
    llvm::GlobalValue*         constant_global       = llvm::dyn_cast<llvm::GlobalValue>(constant);
    llvm::GEPOperator*         gepop                 = llvm::dyn_cast<llvm::GEPOperator>(constant);
    llvm::ConstantExpr*        castop                = llvm::dyn_cast<llvm::ConstantExpr>(constant);

    BaseType* type = p_type_factory->get_type_by_enum(static_cast<TypeID>(constant->getType()->getTypeID()), constant->getType()->getPrimitiveSizeInBits());

    if(type->is_integer_class()) {
        return this->make_constant(type->get_type_identifier(), std::to_string(constant_int->getSExtValue()));
    } else if(type->is_real_class()) {
        if(type->is_float()){
            return this->make_constant(type->get_type_identifier(), std::to_string(constant_float->getValueAPF().convertToFloat()));
        } else if (type->is_double()){
            return this->make_constant(type->get_type_identifier(), std::to_string(constant_float->getValueAPF().convertToDouble()));
        } else {
            assert (0 && "Type not recognized");
        }
    } else if(type->is_struct()) {
        const llvm::StructType* struct_type = llvm::cast<llvm::StructType>(constant->getType());

        std::string aux;

        if(constant->isNullValue()) {
            std::string flattenedtypes = this->get_flattened_types(struct_type);
            std::vector<std::string> tokens = BaseUtils::tokenize(flattenedtypes, VARIABLE_SEPERATOR);

            for (size_t i = 0; i < tokens.size(); i++) {
                aux += this->make_constant(tokens[i],"X");
                aux += VARIABLE_SEPERATOR;
            }
        } else {
            for (size_t i = 0; i < struct_type->getNumElements(); i++) {
                llvm::Value*         operand_i    = constant_struct->getOperand(i);
                llvm::Constant*      operand_i_const = llvm::dyn_cast<llvm::Constant>(operand_i);

                assert(operand_i_const && "Operand i must be constant");
                aux += get_flattened_vals(operand_i_const) + VARIABLE_SEPERATOR;
            }
        }
        return aux;

    } else if(type->is_array()) {
        const llvm::ArrayType* array_type = llvm::cast<llvm::ArrayType>(constant->getType());

        std::string aux;
        if(constant_array) {
            for (size_t i = 0; i < array_type->getNumElements(); i++) {
                llvm::Value*         operand_i    = constant_array->getOperand(i);
                llvm::Constant*      operand_i_const = llvm::dyn_cast<llvm::Constant>(operand_i);
                assert(operand_i_const && "Operand i must be constant");

                aux += get_flattened_vals(operand_i_const) + VARIABLE_SEPERATOR;
            }

        } else if (constant_data_array) {
            // This Constant node has no operands because it stores all of the elements of the constant as densely packed data, instead of as Value*'s.
            int each_element_size = constant_data_array->getRawDataValues().size() / array_type->getNumElements();

            BaseType* element_type = p_type_factory->get_type_by_enum(static_cast<TypeID>(array_type->getElementType()->getTypeID()), array_type->getElementType()->getPrimitiveSizeInBits());
            for (size_t i = 0; i < array_type->getNumElements(); i++) {
                std::string value_str;
                if(element_type->is_int32()) {
                    int value_int = *(constant_data_array->getRawDataValues().data() + i*each_element_size);
                    value_str = std::to_string(value_int);
                } else if(element_type->is_int8()) {
                    char value_char = *(constant_data_array->getRawDataValues().data() + i*each_element_size);
                    value_str = std::to_string(value_char);
                } else if (element_type->is_int16()) {
                    short value_char = *(constant_data_array->getRawDataValues().data() + i*each_element_size);
                    value_str = std::to_string(value_char);
                } else {
                    assert (0 && "Not implemented");
                }
                aux += this->make_constant(element_type->get_type_identifier(), value_str) + VARIABLE_SEPERATOR;
            }
        } else {
            std::string flattenedtypes = get_flattened_types(array_type);
            std::vector<std::string> tokens = BaseUtils::tokenize(flattenedtypes, VARIABLE_SEPERATOR);

            for (size_t i = 0; i < tokens.size(); i++) {
                aux += this->make_constant(tokens[i],"X");
                aux += VARIABLE_SEPERATOR;
            }
        }
        return aux;

    } else if(type->is_pointer()) {
        p_verbose && std::cerr << "Pointer Detected" << std::endl;
        
        if(constant_pointer_null) {
            p_verbose && std::cerr << "Null Pointer Detected!" << std::endl;
            return this->make_constant(type->get_type_identifier(), "0");
        } else if (constant_global) {
            p_verbose && std::cerr << "Pointer to " << constant_global->getName().str() << std::endl;
            std::string value = std::to_string(given_addr["global_" + constant_global->getName().str()]);
            p_verbose && std::cerr << "Address: "<< value << std::endl;
        
            return this->make_constant(type->get_type_identifier(), value);
        } else if(gepop) {
            p_verbose && std::cerr << "GetElementPtr Operation" << std::endl;
            std::string name_base = this->make_global_name(gepop->getOperand(0)->getName().str());
            gepop->getType()->dump();
            std::string offset_tree = this->get_offset_tree(gepop->getType());

         
            int base = given_addr[name_base];
            std::vector<size_t> indexes = get_indexes_gepop(gepop);

            if(p_verbose){
                std::cerr << offset_tree << std::endl;   
                for(auto itor: indexes){
                    std::cerr << itor << std::endl;
                }
            }
            
            p_type_tree->read_tree(offset_tree);
            std::vector<std::pair<size_t, size_t>> alignment = p_type_tree->get_alignment();
            
            int addr = 0;
            if(alignment.size() == 1 && indexes.size() == 2){
                addr = base + indexes[1] * alignment[0].second;
            } else {
                size_t offset = p_type_tree->get_offset(indexes);
                addr = base + offset;
            }
            
            return this->make_constant(type->get_type_identifier(), std::to_string(addr));
        } else if(castop) {
            std::string name_base = this->make_global_name(castop->getOperand(0)->getName().str());
            int base = given_addr[name_base];
            return this->make_constant(type->get_type_identifier(), std::to_string(base));
        } else {
            constant->dump();
            assert(0 && "Error in global pointer initialization");
        }
    } else {
        std::cerr << type << std::endl;
        assert( 0 && "Unknown initializer type");
    }
}

std::vector<size_t> GlobalInitPass::get_indexes_gepop(llvm::GEPOperator* gepop) 
{
    std::vector<size_t> ret;
    
    for(auto it = gepop->idx_begin(); it != gepop->idx_end(); it++) {
        llvm::ConstantInt* CI = llvm::dyn_cast<llvm::ConstantInt>(it->get());
        if(CI) {
            int64_t val = CI->getSExtValue();
            ret.push_back(val);
        } else {
            assert(0 && "non-constant index in gepop");
        }
    }
    return ret;
}
