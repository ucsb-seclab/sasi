// right shift operator crossing the north pole
// plus cast operations from i8 from/to int 32
#define INTERVAL(__p,__x,__a,__b) {if (__p) __x=__a; else __x=__b;}

int main(){
  int p;

  char x1;
  INTERVAL(p,x1,0,127);
  char x2 = x1 + 1; // crossing north pole
  char y1 = x2 >> 3;
  return y1;

  // LVM IR:
  // (1) %x1.0 = phi i8 [ 0, %if.then ], [ 127, %if.else ]  
  // (2) %conv = sext i8 %x1.0 to i32                       
  // (3) %add = add nsw i32 %conv, 1                        
  // (4) %conv3 = trunc i32 %add to i8                      
  // (5) %conv6 = sext i8 %conv3 to i32                     
  // (6) %shr = ashr i32 %conv6, 3                          
  // (7) %conv7 = trunc i32 %shr to i8                      
  // (8) %conv9 = sext i8 %conv7 to i32                     
  // (9) ret i32 %conv9 

  //        classical fixed-width             wrapped 
  // ----------------------------------------------------------------
  // (1)   %x1=[0,127]                       %x1=[0,127]
  // (2)   %conv=[0,127]                     %conv=[0,127]
  // (3)   %add=[1,128]                      %add=[1,128] 
  // (4)   %conv3=[-oo,+oo]                  %conv3=[1,-128]=[0..01,10...0] 
  // (5)   %conv6=[-oo,+oo]                  %conv3=[-128,127]
  // (6)   %shr=[-536870912,536870911]=      %shr=[-16,15]
  //            [11100...0, 00011...1] 
  // (7)   %conv7=[-oo,+oo]                  %conv7=[-16,15]
  // (8)   %conv9=[-oo,+oo]                  %conv9=[-16,15]

}

