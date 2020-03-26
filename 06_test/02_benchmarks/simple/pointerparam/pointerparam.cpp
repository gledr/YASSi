
int function(int* value){
	if(value[2] == 0)
		return 0;
	else
		return 1;
}

int main() {

	int a[6][6];

	function(a[5]);
	
	return 0;
}
