#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}

int main() {
  int x = 100;
  int p;

  INTERVAL(p,x,-1,1);
  while (x != 0)
    x--;
    
  return x;
}
