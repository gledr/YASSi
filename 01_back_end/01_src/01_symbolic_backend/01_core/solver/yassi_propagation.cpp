#include "yassi_propagation.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Backend::Execute::Variables;
using namespace Yassi::Utils;

/**
 * @brief Constructor
 */
Propagation::Propagation(): 
    Object() 
{
    p_memory = Memory::getInstance();
}

/**
 * @brief Destructor
 */
Propagation::~Propagation()
{
    p_memory = nullptr;
}

/**
 * @brief 
 * 
 * @param src 
 * @param dst 
 */
void Propagation::propagate_unary(BaseVariable* src, BaseVariable* dst)
{
    try {
        nullpointer_check(src);
        nullpointer_check(dst);
        
        dst->unset_free_variable();

        PointerVariable* ptr_src = dynamic_cast<PointerVariable*> (src);
        
        if(!(ptr_src && ptr_src->is_function_pointer()) && !src->get_type()->is_void()){
            dst->set_smt_formula(src->get_smt_formula());
        }

        dst->set_propagated_constant();
        if(src->get_propagated_from() != nullptr){
            dst->set_propagated_from(src->get_propagated_from());
        } else {
            dst->set_propagated_from(src);
        }
        
        if(src->is_forced_free()){
            dst->set_force_free();
            p_memory->update_free_variables(dst);
        }
        if(src->get_is_linear()){
            dst->set_is_linear(true);
        }
        if(src->get_index_base_pointer().size() > 0){
            for(auto itor: src->get_index_base_pointer()){
                dst->add_index_base_pointer(itor);
            }
        }
        if(src->get_index_var().size() > 0){
            for(auto itor: src->get_index_var()){ 
                dst->add_index_var(itor);
            }
        }
        for(auto itor: src->get_index_values()){
            dst->insert_index(itor);
        }
        if(src->has_index_assertion()){
            dst->set_index_assertion(src->get_index_assertion());
        }
        
        if(src->is_constant()){
            dst->set_is_linear(true);
        }

        dst->set_sign(src->get_sign());
                
    } catch (std::exception const & exp){
        throw YassiException(exp.what());
    }
}

/**
 * @brief
 * 
 * @param dst
 * @param op1
 * @param op2
 */
void Propagation::propagate_binary(BaseVariable* dst, BaseVariable* op1, BaseVariable* op2) 
{
    nullpointer_check(dst);
    nullpointer_check(op1);
    nullpointer_check(op2);
    
    dst->set_propagated_constant();
    
    if(!op1->is_constant()) {
        if(op1->is_propaged_constant()){
            dst->set_propagated_from(op1->get_propagated_from());
        } else {
            dst->set_propagated_from(op1);
        }
    }
    
    if(!op2->is_constant()){
        if(op2->is_propaged_constant()){
            dst->set_propagated_from(op2->get_propagated_from());
        } else {
            dst->set_propagated_from(op2);
        }
    }
    
    if(op1->get_is_linear() && op2->get_is_linear()){
        dst->set_is_linear(true);
    }
}
