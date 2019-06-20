#include <stdio.h>
int foo() {
  int k = 0;
  while (100> k) {
    int i = 0;
    int j = k;
    while (j > i) {
      i = i + 1;
      j = j - 1;
    }
    k = k + 1;
  }
  return k;
}

int main(int argc, char** argv) {
  printf("%d\n", foo());
}
