// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file BaseRange.cpp
///       Generic Range Variable Class
///
//////////////////////////////////////////////////////////////////////////////

#include "BaseRange.h"

using namespace llvm;
using namespace unimelb;

// #define BITWISE_OP_DEBUG

/// Return true is the range is top.
bool BaseRange::IsTop() const{  
  if (isConstant())  return false;
  return __isTop;

  // if (isSigned){
  //   return (getLB() == APInt::getSignedMinValue(width) &&
  // 	    getUB() == APInt::getSignedMaxValue(width));
  // }
  // else{
  //   return (getLB() == APInt::getMinValue(width) &&
  // 	    getUB() == APInt::getMaxValue(width)) ;
  // }
}


/// Make a range top.
void BaseRange::makeTop(){
  __isTop=true;

  /// This is still needed for abstract operations that can refine top
  /// (e.g., bitwise logical operations)
  if (isSigned){
    setLB(APInt::getSignedMinValue(width));
    setUB(APInt::getSignedMaxValue(width));
  }
  else{
    setLB(APInt::getMinValue(width)); 
    setUB(APInt::getMaxValue(width));
  }
  setStride(1);
}


/// Return true if this and V have syntactically equal bounds.
bool BaseRange::isIdentical(AbstractValue * V){
  BaseRange * B = cast<BaseRange>(V);
  return (__isTop == B->__isTop &&
	  getLB() == B->getLB() && getUB() == B->getUB());
}


/// Display a range.
void BaseRange::printRange(raw_ostream &Out) const{
  if (isBot()){
    Out << "bottom" ; 
    return;
  } 
  if (IsTop()){
    Out << "[-oo,+oo]";
    return;
  }
  Out << "[" 
      << "u:" << LB.toString(10,false) <<"|"<< "s:" << LB.toString(10,true) << "," 
      << "u:" << UB.toString(10,false) <<"|"<< "s:" << UB.toString(10,true) << ","
      << "st:" << getStride() << "]";
}

void BaseRange::print(raw_ostream &Out) const{  
  AbstractValue::print(Out);
  printRange(Out);
}

// Casting operations

/// Check error conditions during casting operations.
void BaseRange::
checkCastingOp(const Type *srcTy, unsigned &srcWidth, 
	       const Type *destTy, unsigned &destWidth,
	       const unsigned OpCode, unsigned ToBeCastWidth){

  assert((Utilities::getIntegerWidth(srcTy ,srcWidth) &&
	  Utilities::getIntegerWidth(destTy,destWidth)) &&
	 "ERROR: allow casting only of integers");  	  
  assert(ToBeCastWidth == srcWidth && "ERROR: violation of some cast precondition");	 
  if (OpCode == Instruction::Trunc)
    assert(srcWidth >= destWidth && "ERROR: violation of Trunc precondition");
  if ((OpCode == Instruction::SExt) || (OpCode == Instruction::ZExt))
    assert(srcWidth <= destWidth && "ERROR: violation of SExt/ZExt precondition");
}

/// Bitwise operations 


// Return true if all conditions about Shift holds.
bool BaseRange::
checkOpWithShift(BaseRange * Op, BaseRange * Shift){  
  // Here just sanity checks
  assert( (Op->getWidth() == Shift->getWidth()) && 
	  "Bitwise operands must have same width");
            // "LB Shift cannot be negative!"
  return (  (!Shift->getLB().isNegative()) &&
	    // "UB Shift cannot be negative!"
	    (!Shift->getUB().isNegative()) &&
	    // "UB Shift cannot be bigger than width!"
	    (Shift->getUB().slt(Op->getWidth())) &&
	    // "Shift does not fit into a uint64_t"
	    (Shift->getWidth() <= 64)  );

} 

/// x=[a,b] and y=[c,d] Reduce the value of x | y by increasing the
/// value of a or c.  We scan a and c from left to right. If both are
/// 1's or 0's then we continue with the scan of the next bit. If one
/// is 1 and the other is 0 then we change the 0 to 1 and set all the
/// following bits to 0's. If that value is less or equal than the
/// corresponding upper bound (if we change a then we compare with c,
/// otherwise we compare with d) we are done. Otherwise, we continue.
int64_t minOr_int64t(int64_t a, int64_t b, int64_t c, int64_t d){
  int64_t m, temp;  
  m = 0x80000000;
  while (m != 0) {
    if (~a & c & m) {
      temp = (a | m) & -m;
      if (temp <= b) {
	a = temp;
	break;
      }
    }
    else if (a & ~c & m) {
      temp = (c | m) & -m;
      if (temp <= d) {
	c = temp;
	break;
      }
    }
    m = m >> 1;
  }
  return a | c;
}

APInt unimelb::
minOr(const APInt &a, const APInt &b, const APInt &c, const APInt &d){
  APInt res(a.getBitWidth(), 
	    minOr_int64t(a.getSExtValue(), b.getSExtValue(), 
			 c.getSExtValue(), d.getSExtValue()));
  return res;
}

/// x=[a,b] and y=[c,d] Increase the value of x | y by decreasing the
/// value of b or d We scan b and d from left to right. If both are
/// 1's then change one to 0 and replace the subsequent bits to
/// 1's. If this value is greater or equal than the corresponding
/// lower bound we are done and the result is b | d. If the change
/// cannot be done we try with the other. If not yet, we continue with
/// the scan.
int64_t maxOr_int64t(int64_t a, int64_t b, int64_t c, int64_t d){
  int64_t m, temp;
  
  m = 0x80000000;
  while (m != 0) {
    if (b & d & m) {
      temp = (b - m) | (m - 1);
      if (temp >= a) {
	b = temp;
	break;
      }
      temp = (d - m) | (m - 1);
      if (temp >= c) {
	d = temp;
	break;
      }
    }
    m = m >> 1;
  }
  return b | d;
}

APInt unimelb::
maxOr(const APInt &a, const APInt &b, const APInt &c, const APInt &d){
  APInt res(a.getBitWidth(), 
	    maxOr_int64t(a.getSExtValue(), b.getSExtValue(), 
			 c.getSExtValue(), d.getSExtValue()));
  return res;
}

/// x=[a,b] and y=[c,d] Reduce the value of x & y by increasing the
/// value of a or c and We scan a and c from left to right. If both
/// are 0's then change one to 1 and all subsequent bits to 0. If this
/// value is less or equal than its corresponding upper bound we are
/// done and the result is a & c. If not, we try with the other
/// value. If it doesn't work neither we continue with the scan.
APInt unimelb::
minAnd(APInt a, const APInt &b, APInt c, const APInt &d){
  APInt m =   APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth()-1);
  while (m != 0){
    if ((~a & ~c & m).getBoolValue()){
      APInt temp = (a | m) &  ~m;
      if (temp.ule(b)){
	a = temp;
	break;
      }
      temp = (c | m) & ~m;
      if (temp.ule(d)){
	c = temp;
	break;
      }
    }
    m = m.lshr(1);
  }
  return a & c;

}

/// x=[a,b] and y=[c,d] Increase the value of x & y by decreasing the
/// value of a or c and We scan b and d from left to right. If one is
/// 0 and the other 1 then change the 1 to 0 and replace the
/// subsequent bits to 1's. If this value is greater or equal than the
/// corresponding lower bound we are done and the result is b & d. If
/// the change cannot be done we try with the other. If not yet, we
/// continue with the scan.
APInt unimelb::
maxAnd(const APInt &a, APInt b, const APInt &c, APInt d){
  APInt m =   APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth()-1);
  while (m != 0){
    if ((b & ~d & m).getBoolValue()){
      APInt temp = (b & ~m) | (m - 1);
      if (temp.uge(a)){
	b = temp;
	break;
      }
    }
    else{
      if ((~b & d & m).getBoolValue()){
	APInt temp = (d & ~m) | (m - 1);
	if (temp.uge(c)){
	  d = temp;
	  break;
	}
      }
    }
    m = m.lshr(1);
  }
  return b & d;
}


APInt unimelb::
minXor(const APInt &a, const APInt &b, const APInt &c, const APInt &d){
  return (unimelb::minAnd(a,b,~d,~c) | unimelb::minAnd(~b,~a,c,d));
}

APInt unimelb::
maxXor(const APInt &a, const APInt &b, const APInt &c, const APInt &d){
  return (unimelb::maxOr(APInt::getNullValue(a.getBitWidth()),
			 unimelb::maxAnd(a,b,~d,~c),
			 APInt::getNullValue(a.getBitWidth()),
			 unimelb::maxAnd(~b,~a,c,d)));
}


void unimelb::
unsignedOr(BaseRange *Op1, BaseRange *Op2, APInt &lb, APInt &ub){
  APInt a = Op1->getLB();   
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();   
  APInt d = Op2->getUB();   

  lb = unimelb::minOr(a,b,c,d);
  ub = unimelb::maxOr(a,b,c,d);

#ifdef BITWISE_OP_DEBUG
  dbgs() << "unsigned OR between ";
  Op1->printRange(dbgs());
  dbgs() << " and  " ;
  Op2->printRange(dbgs());
  dbgs() << "=" ;
  dbgs() << "[" << lb << "," << ub << "]\n";
#endif 

 }

unsigned long unimelb::NumContZeros(unsigned long val){
    if(val == 0) {
        return 0;
    }
    unsigned long y = (~val) & (val-1);
    unsigned count = 0;
    while(y) {
        count++;
        y = y >> 1;
    }
    
    return count;
}

unsigned long unimelb::NumOnes(unsigned long val){
    unsigned count = 0;
    while(val) {
        count++;
        val = val & (val-1);
    }
    
    return count;
}


void unimelb::
unsignedAnd(BaseRange *Op1, BaseRange *Op2, APInt &lb, APInt &ub){

  APInt a = Op1->getLB();   
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();   
  APInt d = Op2->getUB();   
  
  lb = unimelb::minAnd(a,b,c,d);
  ub = unimelb::maxAnd(a,b,c,d);

#ifdef BITWISE_OP_DEBUG
  dbgs() << "unsigned AND between ";
  Op1->printRange(dbgs());
  dbgs() << " and  " ;
  Op2->printRange(dbgs());
  dbgs() << "=" ;
  dbgs() << "[" << lb << "," << ub << "]\n";
#endif 

}


void unimelb::
unsignedXor(BaseRange *Op1, BaseRange *Op2, APInt &lb, APInt &ub){

  APInt a = Op1->getLB();   
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();   
  APInt d = Op2->getUB();   
  
  lb = unimelb::minXor(a,b,c,d);
  ub = unimelb::maxXor(a,b,c,d);

#ifdef BITWISE_OP_DEBUG
  dbgs() << "unsigned XOR between ";
  Op1->printRange(dbgs());
  dbgs() << " and  " ;
  Op2->printRange(dbgs());
  dbgs() << "=" ;
  dbgs() << "[" << lb << "," << ub << "]\n";
#endif 

}



