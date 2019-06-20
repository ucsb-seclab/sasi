#include <stdio.h>

// Run with -inline 300 to avoid limitations with intraprocedural
// analysis.

int foo(int k, int N) {
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
  printf("%d\n", foo(0, 10));
  //  printf("%d\n", foo(30, 100));
 
}
