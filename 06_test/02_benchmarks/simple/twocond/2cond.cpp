int gcd(int a, int b){

	if(a){
		if(b){
			return 0;
		} else {
			return 1;
		}
	} else {
		if(b){
			return 1;
		} else {
			return 2;
		}
	}
}

int main() {
  int _a;
  int _b;
  gcd(_a, _b);
}
