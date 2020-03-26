struct Estructura2{
  int a;
  int b;
};

struct Estructura {
  double entero1;
  int entero2;
  Estructura2 estructura3;
};

Estructura function(Estructura a){
  return a;
}

int main(){
  
  Estructura a;
  
  if(function(a).estructura3.a){
	return 0;
  }  else {
	return 1;
  }
}
