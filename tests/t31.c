int main(int input){
  int y = 0; 
  int x = 90;
  while (input) {  // w/ narrowing
                   // y=[0,0],x=[90,90]
    x = 90; 
                   // y=[0,0],x=[90,90]
    x = x + 1;
                   // y=[0,0],x=[91,91]                 
    y = y + 1;
                   // y=[0,+inf],x=[91,91]                 
  }
  return x+y;
}
