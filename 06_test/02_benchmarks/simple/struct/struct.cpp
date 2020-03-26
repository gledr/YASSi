struct Estructura3 {
	int entero4;
	int entero5;
};

struct Estructura {
	int entero1;
	int entero2;
	struct Estructura3 estructura3;
};

int main(){

	Estructura a;

	if( a.entero1 + a.entero2 + a.estructura3.entero5 > 3 )
		return 0;
	else
		return 1;
}
