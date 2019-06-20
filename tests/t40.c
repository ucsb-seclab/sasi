// test for SExt, ZExt and Trunc

#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}
int main(){
  char x1,y1;
  char x2,y2;
  char x3,y3;
  char z1,z2,z3;
  int p1,p2;

  ////////////////////////////////////////////////////////////////////////////
  // Signed Extension/Truncation
  ////////////////////////////////////////////////////////////////////////////

  INTERVAL(p1,x1,-30,30);
  INTERVAL(p2,y1, 9 ,50);

  // x1 and y1 are signed extended from i8 to i32
  // addition is done with i32
  // the result is truncated to i8 and stored in z1 with i8

  z1 = x1 + y1;  
  // z1 = [-21,80]

  INTERVAL(p1,x2,-30,-5);
  INTERVAL(p2,y2,9,50);

  // x2 and y2 are signed extended from i8 to i32
  // addition is done with i32
  // the result is truncated to i8 and stored in z2 with i8

  z2 = x2 + y2;  
  // z2 = [-21,45]

  INTERVAL(p1,x3,-30,-10);
  INTERVAL(p2,y3,-50,-20);

  // x3 and y3 are signed extended from i8 to i32
  // multiplication is done with i32
  // the result is truncated to i8 and stored in z3

  z3 = x3 * y3;  // the multiplication returns the interval [200,1500] in i32
                 // the conversion to i8 return top since there is overflow
  //z3 is top

  ////////////////////////////////////////////////////////////////////////////
  /// Zero extension/Truncation
  ////////////////////////////////////////////////////////////////////////////

  unsigned char x4,y4;
  unsigned char z4;

  INTERVAL(p1,x4,0U , 128U);
  INTERVAL(p2,y4,30U, 50U);

  // x4 and y4 are unsigned extended from i8 to i32
  //   x4=[0,255] because forcing signed view of x4 ([-128,0]) crosses the south pole. 
  //   y4=[30,50]

  // addition is done with i32 [30,305]
  // the result is truncated to i8 and stored in z4

  z4 = x4 + y4;  
  // z4 is top


  unsigned char x5,y5;
  unsigned char z5;

  INTERVAL(p1,x5,0U , 70U);
  INTERVAL(p2,y5,30U, 50U);

  // x5 and y5 are unsigned extended from i8 to i32
  // the addition is done in i32
  // the result is truncated to i8 and stored in z5

  z5 = x5 + y5;  
  // z5=[20,120]
  
  return 0;
}
