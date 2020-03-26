
int yassi_func(int a){
	return a;
}

int main() {
	int val;
    
	int (*func_pointer)(int) = yassi_func;

	if(func_pointer(val)) return 0;
	else return 1;
}
