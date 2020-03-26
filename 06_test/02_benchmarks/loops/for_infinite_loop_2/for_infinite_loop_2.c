
int main() {
  int x;
  for(;;) {
	  if(x % 3 == 0 ) return 1;
	  if(x % 3 == 1 ) return 2;
	  if(x % 3 == 2 ) return 3;
  }
  return 0;
}
