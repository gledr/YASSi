#include <yassi.hpp>

char a[10];
char* b = a + 1;

int main() {

  __YASSI_force_free_global("a", sizeof(a));
    
	if(*b)
		return 0;
	else
		return 1;
}
