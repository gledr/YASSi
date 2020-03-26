#include <yassi.hpp>

int main() {

  int b = 0;
  __YASSI_force_free_local("b", sizeof(b));
  int c = b;
  if(c > 500) {
	return 1;
  } else {
	return 0;
  }
}
