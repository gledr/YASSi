
typedef struct getopt_data
{
	char *optarg;
	int optind, optwhere;
} getopt_data;


int main() {

	struct getopt_data data;
	if (data.optwhere == 5)
		return 5;
	return 0;
}
