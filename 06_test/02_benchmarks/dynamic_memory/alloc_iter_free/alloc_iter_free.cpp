#include <stdlib.h>

int main() {

  char* x = (char*)malloc(5);
	x++;
	x--;
	free(x);
	return 0;
}

