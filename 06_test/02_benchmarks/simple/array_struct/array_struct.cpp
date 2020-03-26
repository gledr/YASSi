
struct Estructura3 {
	int entero4;
	int entero5;
};

struct Estructura {
	double entero1;
	int entero2;
	struct Estructura3 estructura3;
};

int main(){

	struct Estructura a[10];

	if( a[5].entero1 > 0.5 )
		return 0;
	else
		return 1;
}
