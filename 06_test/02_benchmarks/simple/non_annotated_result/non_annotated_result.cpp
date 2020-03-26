void __VERIFIER_assume(int a);

#include <cstdlib>

int main () {
  int a;
  int b = rand();
  int c = a + b;
  __VERIFIER_assume(b > 0);

  if(c > 42){
	return 0;
  } else {
	return 1;
  }
}

