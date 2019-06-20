// test bitwise operators

#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}

int main(int x1){
  int p;
  int y1,z1;
  int x2,y2,z2;

  INTERVAL(p,y1,1,256);
  z1 = x1 | y1;  

  INTERVAL(p,x2, 0, 15);
  INTERVAL(p,y2,-1048576, 1048560);
  z2 = x2| y2;

  return 0;
}
