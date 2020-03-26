int function(){
	int a;
	return a;
}

int main() {
	if(function()){
	  //CP1
		if(function()){
		  // CP2
			return 1;
		} else {
		  // CP3
			return 2;
		}
	} else {
	  // CP4
		return 3;
	}
}
