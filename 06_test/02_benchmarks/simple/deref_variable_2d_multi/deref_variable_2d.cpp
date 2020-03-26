#include <stdio.h>

int main() {
  
	int index1;
	int index2;
	int array_1[2] = {1,2};
	int array_2[2][2] = {{1,2},{3,4}};

	if(array_1[index1] == 2){
	  printf("1D OKAY\n");
	}
	if(array_2[index2][index1] == 2){
	  printf("2D OKAY\n");
	}

	return 0;
}
