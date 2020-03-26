#include <yassi.hpp>

int division_rest(int val, int const base){
  if(val % base == 0){
	return 0;
  } else {
	return 1;
  }
}

int main () {
  int const c = 2;
  int free;

  return division_rest(free, c);
}
