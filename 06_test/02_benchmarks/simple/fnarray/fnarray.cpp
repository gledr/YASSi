#define SIZE 2

int c[SIZE+1][SIZE+1];// = {0,4,8,12,16,20,24,28,32};

int elem11(int c_param[SIZE+1][SIZE+1]) {

	return c_param[1][1];

}

int main() {

  /*printf("%d\n", elem11(c));*/
	if(elem11(c) == 0)
		return 0;
	else
		return 1;
}
 
