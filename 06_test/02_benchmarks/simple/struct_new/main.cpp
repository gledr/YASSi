struct easy {
  unsigned int a;
  unsigned int b;
};

int main () {

  easy structure;
  structure.b = structure.a + structure.a;

  if(structure.b == 16){
	return 0;
  } else {
	return 1;
  }
}
