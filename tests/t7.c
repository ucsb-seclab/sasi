#include <stdio.h>

// Run with -inline 300 to avoid limitations with intraprocedural
// analysis.

int bar(int i, int j) {
  while (i < j) {
    i = i + 1;
    j = j - 1;
  }
}

int foo(int k, int N) {
  while (k < N) {
    bar(0, k);
    k = k + 1;
  }
  return k;
}

int main(int argc, char** argv) {
  printf("%d\n", foo(0, 100));
}
