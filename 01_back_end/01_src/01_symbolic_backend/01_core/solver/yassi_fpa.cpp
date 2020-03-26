#include "yassi_fpa.hpp"

using namespace Yassi::Backend::Execute;
using namespace Yassi::Types;

size_t const EXCESS8_0 = pow(2,8-1)-1;
size_t const EXCESS11_0 = pow(2,11-1)-1;


/**
 * @brief Constructor
 */
FloatingPointArithmetic::FloatingPointArithmetic() 
{
    p_type_factory = new TypeFactory();
    p_double_type = p_type_factory->get_doubletype();
    p_float_type = p_type_factory->get_floattype();
}

/**
 * @brief Destructor
 */
FloatingPointArithmetic::~FloatingPointArithmetic() 
{
    delete p_type_factory; p_type_factory = nullptr;
}
/**
 * @brief ...
 * 
 * @param sign p_sign:...
 * @param exponent p_exponent:...
 * @param mantissa p_mantissa:...
 * @return std::string
 */
std::string FloatingPointArithmetic::single_precision_to_string(bool const sign, const size_t exponent, const size_t mantissa) 
{
    size_t bits_mantisa = p_float_type->get_fraction() -1;
    /**
     * @brief ...
     * 
     * @param val p_val:...
     * @return size_t
     */
    
    int decoded_exponent = this->excess8_int(exponent);
    float tmp = this->decode_mantisse<float>(bits_mantisa, mantissa);
    float ret_val = pow(-1, (int)sign) * pow(2, decoded_exponent)  * tmp ;
    
    return std::to_string(ret_val);
}

std::string FloatingPointArithmetic::double_precision_to_string(bool const sign, const size_t exponent, const size_t mantissa) 
{
    size_t bits_mantisa = p_double_type->get_fraction() -1;
    
    int decoded_exponent = this->excess11_int(exponent);
    double tmp = this->decode_mantisse<double>(bits_mantisa, mantissa);
    double ret_val = pow(-1, (int)sign) * pow(2, decoded_exponent)  * tmp ;
    
    return std::to_string(ret_val);
}

size_t FloatingPointArithmetic::excess8_int(size_t const & val) 
{
    if(val == EXCESS8_0){
        return 0;
    } else if (val > EXCESS8_0){
        return val - EXCESS8_0;
    } else {
        return val - EXCESS8_0;
    }
}

size_t FloatingPointArithmetic::excess11_int(size_t const & val) 
{
    if(val == EXCESS11_0){
        return 0;
    } else if (val > EXCESS11_0){
        return val - EXCESS11_0;
    } else {
        return val - EXCESS11_0;
    }
}

template <typename T>
T FloatingPointArithmetic::decode_mantisse(int size, size_t decode_mantisse) 
{
    T ret_val = 1.0;
    std::vector<bool> bin_val = this->dec2bcd(size, decode_mantisse);

    for(size_t i = 0; i < bin_val.size(); ++i){
        int exp = (-1) * (i+1);
        if(bin_val[i] == 1){
            T tmp_val = ret_val;
            T increment = pow(2, exp);
            ret_val = tmp_val + increment;
        }
    }
    
    return ret_val;
}

std::vector<bool> FloatingPointArithmetic::dec2bcd(size_t const bit_width, size_t const dec_val)
{
    int current_val = static_cast<int>(dec_val);
    std::vector<bool> bin_val;
    bin_val.resize(bit_width);
    size_t bit_pos = bit_width-1;

     while(current_val >= 0) {
        size_t tmp = current_val;
        current_val = tmp / 2;
        size_t bit = tmp % 2;
        bin_val[bit_pos--] = bit;

        if(current_val == 0){
            break;
        }
    }
    return bin_val;
}
