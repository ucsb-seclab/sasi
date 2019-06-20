// if we run with -instcombine then -wrapped-analysis is more precise
// since foo return always -128 while -range-analysis will return top.
// The need of -instcombine is due to some difficulties for using
// branch conditions to refine values in presence of casting
// instructions.

signed char foo(){
  signed char i=0;
  while (i>=0){
    i=i+1;
  }
  return i; // fixed-width intervals [-128,-1]
            // wrapped intervals     [-128,-128]
}

int main(){
  printf("%d",foo());
}
