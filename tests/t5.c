#include <stdio.h>

// Run with -inline 300 to avoid limitations of intraprocedural
// analysis and also with -instcombine to avoid dramatic losses of
// precision due to cast instructions.

int foo(char k, char N) {
  while (k < N) {
    int i = 0;
    int j = k;
    while (i < j) {
      i = i + 1;
      j = j - 1;
    }
    k = k + 1;
  }
  return k;
}

int main(int argc, char** argv) {
  printf("%d\n", foo(0, 100));
}
