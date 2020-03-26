
int main () {

  	char* ar[] = {"zz"};
	__FOREST_force_free_local("ar", sizeof(ar));
	if( ar[0][0] == 'a' )
		return 1;
	else
		return 0;
}

