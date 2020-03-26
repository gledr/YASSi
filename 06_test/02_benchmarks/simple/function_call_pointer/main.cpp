int fuu(int * bar){
  return (*bar)+(*bar);
}

int main () {
  int val;
  int * ptr = &val;
  if (fuu(ptr) > 10){
	return 0;
  } else {
	return 1;
  }
}
