

class  Klasse {
public:
  Klasse(){
	b = 12;
  }
  ~Klasse(){
	b = 0;
  }
	
  
  int doit(){
	if (this->calc() + b == 42){
	  return 0;
	} else {
	  return 1;
	}

  }
private:
  int calc(){
	int a;
	return a;
  }
  int b;
};


int main (){
  Klasse k;
  return k.doit();
}
