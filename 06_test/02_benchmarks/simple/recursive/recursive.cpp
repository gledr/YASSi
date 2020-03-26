int fn(int x){
	if(x == 1) return 0;
	else return fn(x-1);
}

int main() {
	int x;
	 fn(x);

	 if(x){
	   return 0;
	 } else {
	   return 1;
	 }
}
