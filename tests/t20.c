// Example provided by Andre Oliveira Maroneze.
// This example showed a bug in the wrapped interval analysis
// implementation.
// This bug was fixed (06/02/13).
int main() {
  int i, j;
  for (i=0; i<5; i++)
    for(j=5; j>=0; j--);
  return i+j;
}
