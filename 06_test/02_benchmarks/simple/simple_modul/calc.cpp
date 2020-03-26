#include "calc.hpp"

static int inc(int a);

int add(int a, int b){

  int tmp = inc(a);
  int c = tmp + b ;
 
  if(c == 42){
	return 0;
  } else {
	return 1;
  }
}

int inc(int a){
  return a+1;
}
