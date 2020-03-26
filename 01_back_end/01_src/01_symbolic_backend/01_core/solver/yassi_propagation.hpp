#ifndef PROPAGATION_HPP
#define PROPAGATION_HPP

#include <string>

#include <yassi_object.hpp>
#include <yassi_variables.hpp>
#include <yassi_memory.hpp>
#include <yassi_exception.hpp>

namespace Yassi::Backend::Execute {

class Propagation : public virtual Object {
public:
    Propagation();
  
    virtual ~Propagation();
  
    void propagate_unary(Variables::BaseVariable* src, Variables::BaseVariable* dst);
    
    void propagate_binary(Variables::BaseVariable* dst, Variables::BaseVariable* op1, Variables::BaseVariable* op2);
   
private:
    Memory* p_memory;
};

}

#endif /* PROPAGATION_HPP */
