int yassifunc(){
  int a;
  return a;
}

int main() {
	
	int (*func_pointer)() = yassifunc;

	if(func_pointer()) return 0;
	else return 1;
}
