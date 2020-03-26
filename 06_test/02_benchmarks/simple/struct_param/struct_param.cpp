struct Estructura2{
	int a;
	int b;
};

struct Estructura {
	double entero1;
	int entero2;
	struct Estructura2 estructura3;
};

int function(struct Estructura a){
	return a.estructura3.a;
}

int main(){

	struct Estructura a;

	if( function(a) )
		return 0;
	else
		return 1;
}
