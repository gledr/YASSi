
int main() {
  double a = 1.25;
  double b;
  double c = a+b;

  __VERIFIER_assume(b < 50.0);
  __VERIFIER_assume(b > 0.0);
  
  if(c > 42.1){
	return 0;
  } else {
	return 1;
  }
}
