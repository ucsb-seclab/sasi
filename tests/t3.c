#include <stdio.h>

int foo(int k) {
  while (k < 10000) {
    int i = 0;
    int j = k;
    while (i < j) {
      i = i + 1;
      j = j - 1;
      // i=[0,98], j=[1,99]
    }
    k = k + 1;
    // k=[-2147483647,100]
  }
  return k;
}

int main(int argc, char** argv) {
  printf("%d\n", foo(argc));
}
