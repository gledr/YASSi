#include <yassi.hpp>

int main(){

	float a;
	float b;
	float c = 4.0f;

	__VERIFIER_assume(a < 3.0f);
	__VERIFIER_assume(b < 3.0f);

	__VERIFIER_assume(a > 0.0f);
	__VERIFIER_assume(b > 0.0f);
	
	if( a+b > c)
		return 0;
	else
		return 1;

}
