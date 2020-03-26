#include <yassi.hpp>

int getopt (char *optstring) {

	if(optstring == 0) return 0;
	return 1;
}

int main() {
  char * string;
  __FOREST_force_free_local("string", sizeof(string));

  if(getopt(string)){
	return 0;
  } else {
	return 1;
  }
}

