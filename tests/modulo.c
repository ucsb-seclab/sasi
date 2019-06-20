/* 

  - With unlimited precision the code after the loop is unreachable.
  - With fixed-width precision the return value is [-128,11].
  - With wrapped intervals the return value is [-128,-119]

  We need to run with -instcombine due to some difficulties for using
  branch conditions to refine values in presence of casting
  instructions.
*/

char modulo(char x, char y, int p){
  y=-10;
  if(p) x=0;
  else  x=100;
  while (x >= y){
    x = x-y;
  }
  return x;
}

int main(){
  int a,b;
  int p;
  printf("%d\n",modulo(a,b,p));
  return 0;
}
