
int main() {

  int  firstvalue;
  int  secondvalue;

  int * mypointer;

  mypointer = &firstvalue;
  *mypointer = 10;

  mypointer = &secondvalue;
  
  if(*mypointer == firstvalue){
	return 0;
  } else {
	return 1;
  }
}
