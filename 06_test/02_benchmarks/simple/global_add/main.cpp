
int a;

int main () {
 
  __FOREST_force_free_global("a", sizeof(a));
    
  int b = a + 5;

  if(b == 25){
	return 1;
  } else {
	return 0;
  }
}
