// test division and modulo operations

#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}
int main(){
  int p1,p2;

  int x1,y1,z1,z2,z3,z4;
  int x2,y2,z5,z6;
  int x3,y3,z7;
  int x4,y4,z8;
  int x5,y5,z9;
  int x6,y6,z10;

  INTERVAL(p1,x1,2,3);
  INTERVAL(p2,y1,9,10);

  z1 = x1 / y1;  // z1=[0,0]  
  z2 = x1 % y1;  // z2=[0,9]

  z3 = y1 / x1;  // z3 = [3,5] 
  z4 = y1 % x1;  // z4 = [0,2]

  INTERVAL(p1,x2,-50,60);
  INTERVAL(p2,y2,-15,10);

  z5 = x2 / y2;   // z5 = [-60, 60] 
  z6 = y2 / x2;   // z6 = [-15,15]

  INTERVAL(p1,x6,-24,24);
  INTERVAL(p2,y6,-3,3);

  z10 = x6 / y6; // z10 = [-24,24]

  INTERVAL(p1,x3,12,14);
  INTERVAL(p2,y3,-5,-3);

  z7 = x3 % y3; // z7 = [0,4]

  INTERVAL(p1,x4,-14,-12);
  INTERVAL(p2,y4,3,5);

  z8 = x4 % y4; // z7 = [-4,0]

  INTERVAL(p1,x5,-104,200);
  INTERVAL(p2,y5,20,45);

  z9 = x5 % y5; // z7 = [-44,44]
    
  return 0;
}
