int main(){
  unsigned q1, q2;
  unsigned p1,p2,p3;
  unsigned x,y,z,w,r;
  unsigned a,b,c,x1,x2,x3,x4;

  p1=8;
  c=0;
  // then-definite guard
  if (p1 > 5)
    x=4;
  else
    x=7;

  // x=[4,4]
  
  // (undefined) maybe 
  if (p2 > 10)
    y=6;
  else
    y=10;

  // y=[6,10]

  // (defined) maybe 
  if (q1 > q2)
    w=6;
  else
    w=2;

  // w=[2,6]

  // maybe
  if (q2>0){
    a=0;
    b=30;
    x1=10;
    x2=100;
    x3=0;
    x4=0;
  }
  else{
    a=100;
    b=50;
    x1=40;
    x2=400;
    x3=50;
    x4=50;

  }

  // a=[0,100]
  // b=[30,50]

  // maybe because a>b and a<=b are possible
  if (a>b)
    c=100;

  // c=[0,100]

  if (a==b)   // maybe because a==b and !a==b are possible
    c=200;

  // c=[0,200]

  if (x1==x2)   // definite false
    c+=100;

  //  if (! (x3 == x4))  // definite true
  //    c+=100;
  if (x3 == x4)
    c+=1000;    // c= [1000,1200]
  else
    c+=100;     // c=[100,300]

  // c= [100,1200]

  p3=5;
  // else-definite guard
  if (p3 > 10)
    z=6;
  else
    z=10;

  // z= [10,10]

  r=x+y+w+z-a-b+c;    

  // r = [4,4] + [6,10] + [2,6] + [10,10] - [0,100] - [30,50] + [100,1200]
  // r = [122,1230] - [30,150] = [-28, 1200]

  return r;
}
