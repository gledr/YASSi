#ifndef FLOATINGPOINTARITHMETIC_HPP
#define FLOATINGPOINTARITHMETIC_HPP

#include <string>
#include <cmath>
#include <vector>
#include <algorithm>
#include <sstream>

#include <yassi_types.hpp>
#include <yassi_exception.hpp>

namespace Yassi::Backend::Execute {

class FloatingPointArithmetic {
public:
    FloatingPointArithmetic();
    
    ~FloatingPointArithmetic();
    
    std::string single_precision_to_string(bool const sign, size_t const exponent, size_t const  mantissa);
    
    std::string double_precision_to_string(bool const sign, size_t const exponent, size_t const  mantissa);
    
private:
    Yassi::Types::FloatType * p_float_type;
    Yassi::Types::DoubleType * p_double_type;
    Yassi::Types::TypeFactory * p_type_factory;
    
    size_t excess8_int(size_t const & val);
    size_t excess11_int(size_t const & val);
    
    template <typename T>
    T decode_mantisse(int size, size_t decode_mantisse);
    
    std::vector<bool> dec2bcd(size_t const bit_width, size_t const dec_val);
};

}

#endif /* FLOATINGPOINTARITHMETIC_HPP */
