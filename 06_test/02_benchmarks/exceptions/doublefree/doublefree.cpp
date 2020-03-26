#include <stdlib.h>

int main() {
	char* a = (char*)malloc(5);
	
	free(a);
	free(a);
	
	return 0;
}
