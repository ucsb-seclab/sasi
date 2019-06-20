// Here we can infer that j=[0,101] and i=[101,101]
// We should get also j=[101,101] but we cannot because for exit block
// we can only use the condition %tmp= icmp slt i32 %i.0, 101

int main(){
  int i=0;  
  int j=0;
  while (i <= 100){
    while (j <= 100){
      j++;
    }
    i++;
  }        
  return i+j;  
}
