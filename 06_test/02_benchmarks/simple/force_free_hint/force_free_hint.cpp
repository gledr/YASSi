
int fn(){
	int var_a = 1;
    
    __FOREST_force_free_local("var_a", sizeof(var_a));
    
	if(var_a)
		return 1;
	else
		return 0;
}

int fn_1(){
	int a = 1;
    
    __FOREST_force_free_local("a", sizeof(a));
    
	if(a)
		return 1;
	else 
		return 0;
}

int main() {
	fn();
	fn_1();
	return 0;
}
