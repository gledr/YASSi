struct Estructura3 {
	int entero4;
	int entero5;
};

struct Estructura {
	double entero1;
	int entero2;
	struct Estructura3 estructura3;
};

struct Estructura a;

int main(){

	if( a.estructura3.entero5 > 0 )
		return 0;
	else
		return 1;
}
