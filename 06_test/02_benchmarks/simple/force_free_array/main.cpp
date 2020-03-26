
int main ()
{
  int arr[] = {0,1,2};
  __FOREST_force_free_local("arr", sizeof(arr));

  if(arr[1] == 4){
	return 0;
  } else {
	return 1;
  }
}
