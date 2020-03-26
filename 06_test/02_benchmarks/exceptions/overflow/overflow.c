#include <stdio.h>

void my_strcpy(char dest[], const char source[]) {
	int i = 0;
	while (1) {
		dest[i] = source[i];
		if (dest[i] == '\0') break;
		i++;
	}
}

int my_strcmp(char* s1, char* s2)
{
    while(*s1 && (*s1==*s2))
        s1++,s2++;
    return *(unsigned char*)s1-*(unsigned char*)s2;
}

int main(int argc, const char *argv[])
{

	char password_buffer[10];
	int acceso = 0;
	my_strcpy(password_buffer, argv[1]);

	if(!my_strcmp(password_buffer, "clave"))
		acceso = 1;

	if( acceso )
		printf("Acceso Permitido\n");
	else 
		printf("Acceso Denegado\n");

	return 0;
	
}

