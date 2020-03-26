int main() {


	int variable[5];

	int* pointer = variable;

	pointer += 2;

	if( *pointer == 2 )
		return 0;
	else
		return 1;
}
