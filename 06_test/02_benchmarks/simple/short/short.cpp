#include <yassi.hpp>

short a_gl;

int main() {
  __YASSI_force_free_global("a_gl", sizeof(a_gl));
    
	short a_lc;
	if(a_lc)
		return 0;

	if(a_gl)
		return 1;

	return 2;
}
