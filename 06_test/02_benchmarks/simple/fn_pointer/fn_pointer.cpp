void funcion(void){
  return;
}

int main() {
  
	void (*fn)(void) = funcion;
	fn();

	return 0;
}
