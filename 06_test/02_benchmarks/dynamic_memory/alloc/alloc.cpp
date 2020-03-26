#include <stdlib.h>

int main() {
  char* a = (char*)malloc(5);
  char ret_val;
	if(a[1])
	  ret_val = 0;
	else
	  ret_val = 1;

	free(a);

	return ret_val;
}
