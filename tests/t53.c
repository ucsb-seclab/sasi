// right shift operator crossing the north pole

#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}

int main(){
  int p;

  int x1;
  INTERVAL(p,x1,0,2147483647);  // x1=[0,2147483647] 
  // crossing north pole
  int x2 = x1 + 1;   // if wrapped: x2 = [1,-2147483648] (for clarity, signed view)
  int y1 = x2 >> 28; // if wrapped: y1= [0,-8]
  // with classical fixed-width x2 is top already since we cross the
  // north pole
  return y1;
}

