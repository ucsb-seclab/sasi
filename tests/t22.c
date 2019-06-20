int main( int argc, char* argv[] ){

  int x = 100;
  int i = 0;
  while (x > 0){
    x = x / 2;
    i = i + 1;
  }
  printf("Value %d\n",i);
  return i;
}
