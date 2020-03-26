#include <yassi.hpp>

int a;
int* b = &a;

int main() {
  __YASSI_force_free_global("a", sizeof(a));
  
	if(*b)
		return 0;
	else
		return 1;
}
