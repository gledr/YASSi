int data[2];

int main() {
    int seed;
    __FOREST_force_free_local("seed", sizeof(seed));

        seed = 0;
    for (unsigned int i = 0; i < 2; i++) {
        seed = ((seed * 133) + 81) % 65535;
        data[i] = seed;
    }

    if( data[1] == 31416 )
        return 0;
    else
        return 1;
}
