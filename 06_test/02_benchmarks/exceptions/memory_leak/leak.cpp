#include <stdlib.h>

int main() {
  char* a = (char*)malloc(5);
  
  if(a[1])
	return 0;
  else
	return 1; 
}
