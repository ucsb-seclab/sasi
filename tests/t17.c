int main(){
  int x=0;
  int y=1;
  int z;
  int h;

  while (x<1000){
    x++;
    y = x / 2;
    h = y % x;
    y++;
  }  
  z=x+y+h;
  return z;
}
