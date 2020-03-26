
int a;

int main() {

  __FOREST_force_free_global("a", sizeof(a));
	a = 1 - a;
	
	if( a == 5 )
		return 0;
	else
		return 1;

}
