#include <stdlib.h>

int main() {
	int* a = (int*)malloc(8);
	if(a[1])
		return 0;
	else
		return 1;

	free(a);
}
