#include <yassi.hpp>

int b;
extern int a;

int main() {
  __YASSI_force_free_global("a", sizeof(a));
  __YASSI_force_free_global("b", sizeof(b));
  
	if(a)
		return 0;
	else
		return 1;
}
