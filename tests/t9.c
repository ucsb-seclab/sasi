int main(int input) {
  int z;
  int i = 0, j = 0;
  while (i < 10) {
    i++;
    if (input)
      j = 2 * i;
  }  
  z = i+j;
  return z;
}
