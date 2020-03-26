
int main() {

    int a = 5;
    
    __FOREST_force_free_local("a", sizeof(a));
    
	if( a == 5 )
		return 0;
	else
		return 1;
}
