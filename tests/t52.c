// right shift operator

#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}

int main(){

  int p1,p2;
  int x1,y1;

  INTERVAL(p1,x1,0,0); 
  INTERVAL(p2,y1,0,23456789); 
    
  while (y1 > x1){
      y1 = y1 >> 1;
  }
  return y1;
}

