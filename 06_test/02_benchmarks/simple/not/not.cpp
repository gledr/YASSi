int main() {
	char a;
	char b = ~a;

	char c = -6;
	char d = -252;

	if(b == c)
		return 0;

	if(b == d)
		return 1;

	return 2;
}
