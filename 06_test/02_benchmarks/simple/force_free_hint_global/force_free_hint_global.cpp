
int a;

int main() {
  __FOREST_force_free_global("a", sizeof(a));
	if(a)
		return 0;
	else
		return 1;
}
