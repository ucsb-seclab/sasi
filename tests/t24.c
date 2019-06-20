// widening
#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}

int main(){

  int p;
  int x,y;

  INTERVAL(p,x,-1073741825,1073741822); 
    
  while (x >= 0){
    x = x - 1;
  }
  return x;
}

