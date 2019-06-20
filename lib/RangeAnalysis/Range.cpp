// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file RangeLattice.cpp
///       Classical fixed-width Interval Abstract Domain.
///
/// \todo There are still memory leaks: need to fix.
//////////////////////////////////////////////////////////////////////////////
#include "BaseRange.h"
#include "Range.h"

#include <algorithm> // std::min_element, std::max_element
 
//#define DEBUG_TYPE "RangeAnalysis"
//#define DEBUG_CAST_OP

#define CHECK_WELLFORMED 

STATISTIC(NumOfOverflows     ,"Number of overflows");

using namespace llvm;
using namespace unimelb;

#ifdef CHECK_WELLFORMED 
// Important debugging function to make sure all intervals are
// well-formed.
void CheckIntervalIsWellFormed(Range *I, std::string CallerName){
  if (I->isBot() || I->IsTop()) return;
  if (I->IsSigned()){
    if (!I->getLB().sle(I->getUB())){
      dbgs() << "After " << CallerName << "\n";
      Instruction * Ins = cast<Instruction>(I->getValue());
      I->print(dbgs());
      dbgs() << " defined in function " 
	     <<  Ins->getParent()->getParent()->getName() << "\n";
      llvm_unreachable("The interval is not well formed!");
    }
  }
  else{
    if (!I->getLB().ule(I->getUB())){
      dbgs() << "After " << CallerName << "\n";
      Instruction * Ins = cast<Instruction>(I->getValue());
      I->print(dbgs());
      dbgs() << " defined in function " 
	     <<  Ins->getParent()->getParent()->getName() << "\n";
      llvm_unreachable("The interval is not well formed!");
    }
  }
}
#endif /*CHECK_WELLFORMED*/

// Return true if S is crossing the north pole (i.e., from 0111....1
// to 1000...0)
bool Range::isCrossingNorthPole(Range * S) {
  unsigned width    = S->getWidth();
  unsigned isSigned = S->IsSigned();

  APInt NP_lb = APInt::getSignedMaxValue(width); // 0111...1
  APInt NP_ub = APInt::getSignedMinValue(width); // 1000...0
  Range NP(NP_lb,NP_ub,width,isSigned);

  return NP.lessOrEqual(S);
}

/// Auxiliary method to cut at the south pole to perform signed
/// versions of the bitwise logical operations.
std::vector<RangePtr> 
ssplit(const APInt &x, const APInt &y, unsigned width, bool IsSigned){

  // Temporary wrapped interval for south pole
  APInt SP_lb = APInt::getMaxValue(width); // 111...1
  APInt SP_ub(width, 0,IsSigned);          // 000...0 
  Range SP(SP_lb,SP_ub,width,IsSigned);
  // Temporary wrapped interval 
  RangePtr s(new Range(x,y,width,IsSigned));

  std::vector<RangePtr> res;
  if (SP.lessOrEqual(s.get())){
    // Split into two intervals
    RangePtr s1(new Range(x,SP_lb,width,IsSigned)); // [x, 111....1]
    RangePtr s2(new Range(SP_ub,y,width,IsSigned)); // [000...0,  y] 
    res.push_back(s1);
    res.push_back(s2);
  }
  else{  
    // No need of split
    res.push_back(s);
  }
  return res;  
}

/// Return true if the range is empty 
bool Range::isBot() const{
  if (isConstant())  return false;      
  if (isSigned)
    return ((getLB() == APInt::getSignedMaxValue(width)) && 
	    (getUB() == APInt::getSignedMinValue(width)));
  else
    return ((getLB() == APInt::getMaxValue(width)) && 
	    (getUB() == APInt::getMinValue(width)));
}

/// Make an empty range.
void Range::makeBot() {
  if (isSigned){
    setLB(APInt::getSignedMaxValue(width));
    setUB(APInt::getSignedMinValue(width));
  }
  else{
    setLB(APInt::getMaxValue(width));
    setUB(APInt::getMinValue(width));
  }
  __isTop=false;
}  


bool Range::IsTop() const  { 
  return BaseRange::IsTop();
}

void Range::makeTop() { 
  BaseRange::makeTop();
}


/// Auxiliary method to refine top whenever it is an operand of a
/// binary bitwise logical operation and the other operand is not top.
Range convertTopToNumInterval(Range *Op, bool IsSigned){
  if (Op->IsTop()){
    Range Tmp(*Op);
    
    // This is important otherwise, top flag may persist.
    Tmp.resetTopFlag();

    if (IsSigned){
      Tmp.setLB(APInt::getSignedMinValue(Op->getWidth()));
      Tmp.setUB(APInt::getSignedMaxValue(Op->getWidth()));
    }
    else{
      Tmp.setLB(APInt::getNullValue(Op->getWidth()));
      Tmp.setUB(APInt::getMaxValue(Op->getWidth()));
    }
    return Tmp;
  }      
  return *Op;
}

/// Return true if the range of this is included in the the range of V
/// lessOrEqual([l1,u1],[l2,u2]) = true iff l2<=l1 and u1<=u2 
/// (i.e., [l1,u1] is included in [l2,u2])  
bool Range::lessOrEqual(AbstractValue* V){
  // Simple cases first: bottom and top
  if (isBot())  return true;  
  Range *I =  cast<Range>(V);    
  if (IsTop() && I->IsTop()) 
    return true;
  else{
    if (IsTop())
      return false;
    else{
      if (I->IsTop()) 
	return true;
    }
  }
  // General case
  APInt l1 = getLB();
  APInt u1 = getUB();
  APInt l2 = I->getLB();
  APInt u2 = I->getUB();    
  assert(IsSigned() == I->IsSigned() 
	 && "Arguments must have same signedeness");
  if (I->IsSigned()) 
    return ( l2.sle(l1) &&  u1.sle(u2) );
  else 
    return ( l2.ule(l1) &&  u1.ule(u2) );
}

/// Compute the join operation of two ranges and store the result in
/// this.  This operation is an overapproximation of the true union.
/// join([a,b],[c,d]) = [min(a,c),max(b,c)]
void Range::join(AbstractValue * V){
  Range *I2 = cast<Range>(V);
  Range *I1 = this;      
  // assert(I1->IsSigned() == I2->IsSigned() 
  //	 && "Arguments must have same signedeness");

  DEBUG(dbgs() << "\t" << *I1 << " join " << *I2 << " --> ");      

  // Catch simple cases first (bottom, top)
  if (I1->isBot() && I2->isBot()){
    makeBot();
    goto END;
  }
  if (I1->IsTop() || I2->IsTop()){
    makeTop();
    goto END;
  }
  // General case:
  if (I1->isSigned){
    setLB(smin(I1->getLB(), I2->getLB()));
    setUB(smax(I1->getUB(), I2->getUB()));
  }
  else{
    setLB(umin(I1->getLB(), I2->getLB()));
    setUB(umax(I1->getUB(), I2->getUB()));
  }
    
 END:
  normalizeTop();
  DEBUG(dbgs() << *this << "\n");
}

/// Compute the meet operation of two ranges V1 and V2 This operation
/// is the exact intersection.
///
///                          if [a,b] or [c,d] is bot    then [l,h] = bot
/// meet([a,b],[c,d])=[l,h]  if is_disjoint([a,b],[c,d]) then [l,h] = bot
///                          else l = max(a,c) and h=min(b,d)
void Range::meet(AbstractValue *V1, AbstractValue *V2){

  assert(!isConstant() 
	 &&  "meet can be only called by a non-constant value");

  Range *I1 = cast<Range>(V1);
  Range *I2 = cast<Range>(V2);

  // Catch simple cases first 
  if (I1->isBot() || I2->isBot()){	
    makeBot();
    return;
  }

  if (I1->isSigned    && signedIsDisjoint(I1->getLB(),I1->getUB(),
					 I2->getLB(),I2->getUB())) {
    makeBot();
    return;
  }
  if ((!I1->isSigned) && IsDisjoint(I1->getLB(),I1->getUB(),
				    I2->getLB(),I2->getUB())) {
    makeBot();
    return;
  }  

  if (I1->isSigned){
    setLB(smax(I1->getLB(), I2->getLB()));    
    setUB(smin(I1->getUB(), I2->getUB()));
  }
  else{
    setLB(umax(I1->getLB(), I2->getLB()));
    setUB(umin(I1->getUB(), I2->getUB()));
  }
  
  return;
}

bool Range::isIdentical(AbstractValue *V){
  return BaseRange::isIdentical(V);
}

bool Range::isEqual(AbstractValue *V){
  Range *S = this;
  Range *T = cast<Range>(V);    
  // This is correct since we have a lattice and hence, the
  // antisymmetric property holds.
  return (S->lessOrEqual(T) && T->lessOrEqual(S));
}

/// Compute the naive Cousot&Cousot'76 widening operation between two
/// ranges PreviousV and CurrentV and store the result in this.
/// widen([a,b],[c,d]) =  [l,h] where   
/// if b >= d then h=b else h=MAXINT
/// if a <= c then l=a else l=MININT
void wideningCousot77(Range *PreviousI, Range *CurrentI){

  assert(PreviousI->IsSigned() == CurrentI->IsSigned() 
	 && "Arguments must have same signedeness");

  if (PreviousI->IsSigned()){
    // signed case
    if (PreviousI->getUB().sge(CurrentI->getUB()))
      CurrentI->setUB(PreviousI->getUB());
    else{
      // (*) To push only the upper bound to MAXINT is not correct. We
      // need to cover also the case when the range may
      // wraparound. This is why we need to go to "top".
      // CurrentI->setUB(APInt::getSignedMaxValue(PreviousI->getWidth()));      
      CurrentI->makeTop();
    }    
    if (PreviousI->getLB().sle(CurrentI->getLB()))
      CurrentI->setLB(PreviousI->getLB());
    else{
      //  (*)
      // CurrentI->setLB(APInt::getSignedMinValue(PreviousI->getWidth()));
      CurrentI->makeTop();
    }
  }
  else{
    // unsigned case
    if (PreviousI->getUB().uge(CurrentI->getUB()))
      CurrentI->setUB(PreviousI->getUB());
    else{
      // (*)
      // CurrentI->setUB(APInt::getMaxValue(PreviousI->getWidth()));
      CurrentI->makeTop();
    }
    
    if (PreviousI->getLB().ule(CurrentI->getLB()))
      CurrentI->setLB(PreviousI->getLB());
    else{
      // (*)
      // CurrentI->setLB(APInt::getMinValue(PreviousI->getWidth()));
      CurrentI->makeTop();
    }
  }      
}

/// Compute the widening operation taking a "jump" making the interval
/// much wider. Compute a finite set of "jump points" J (e.g., the set
/// of all integer constants in the program augmented with MININT and
/// MAXINT). Then, widen([l,u])=[max{x \in J | x <=l},min{x \in J,u <= x}]
/// That is, it chooses the greatest of the constants that is smaller
/// than lb and the smallest of the constants that it is bigger than ub.
#if 0
void widenOneInterval(Range * Rng, const std::vector<int64_t> &JumpSet, 
		      APInt &lb, APInt &ub){

  // Initial values 
  if (Rng->IsSigned()){
    lb= APInt::getSignedMinValue(Rng->getWidth());
    ub= APInt::getSignedMaxValue(Rng->getWidth());
  }
  else{
    lb= APInt::getMinValue(Rng->getWidth());
    ub= APInt::getMaxValue(Rng->getWidth());
  }

  for (unsigned int i=0 ; i<JumpSet.size() ; i++){
    APInt LandMark(Rng->getWidth(), JumpSet[i], Rng->IsSigned());
    if (Rng->IsSigned()){
      if (Rng->getLB().sgt(LandMark)) 
	lb = BaseRange::smax(lb,LandMark) ; 
      if (Rng->getUB().slt(LandMark)) 
	ub = BaseRange::smin(ub,LandMark) ;
    }
    else{
      if (Rng->getLB().ugt(LandMark)) 
	lb = BaseRange::umax(lb,LandMark);
      if (Rng->getUB().ult(LandMark)) 
	ub = BaseRange::umin(ub,LandMark);
    }
  }

  DEBUG(dbgs() << "Widen interval based on landmarks: " 
	<< "widen([" << Rng->getLB() << "," << Rng->getUB() << "]) ="
	<< "[" << lb << "," << ub << "]\n");
}
#else
/////
// Optimized version that speed up the analysis significantly.
// This version takes advantage of the fact that JumpSet is sorted.
/////
void widenOneInterval(Range * Rng, const std::vector<int64_t> &JumpSet, 
		      APInt &lb, APInt &ub){

  assert(Rng->IsSigned()); // assuming signed integers
  unsigned int width = Rng->getWidth();
  /////////////////////////////////////////////////////////////////
  // lb_It points to the first element that is not less than lb
  /////////////////////////////////////////////////////////////////
  std::vector<int64_t>::const_iterator lb_It= 
    std::lower_bound(JumpSet.begin(), JumpSet.end(), Rng->getLB().getSExtValue());
  if (lb_It == JumpSet.end()) // nobody is smaller than Rng->getLB()
    lb = APInt::getSignedMinValue(width);
  else{  
    int64_t MIN = APInt::getSignedMinValue(width).getSExtValue();
    int64_t cand;
    ( (lb_It == JumpSet.begin())? cand = *lb_It : cand = *(lb_It - 1));
    if (cand < MIN)
      lb = APInt::getSignedMinValue(width);
    else{
      APInt LB_LandMark(Rng->getWidth(), cand, Rng->IsSigned());
      lb=LB_LandMark;
    }
  }
  /////////////////////////////////////////////////////////////////
  // ub_It points to the first element that is greater than ub
  /////////////////////////////////////////////////////////////////
  std::vector<int64_t>::const_iterator ub_It= 
    std::upper_bound(JumpSet.begin(), JumpSet.end(), Rng->getUB().getSExtValue());
  if (ub_It == JumpSet.end()) // nobody is greater than Rng->getUB()
    ub = APInt::getSignedMaxValue(width);
  else{
    int64_t MAX = APInt::getSignedMaxValue(width).getSExtValue();
    if (*ub_It > MAX)
      ub = APInt::getSignedMaxValue(width);
    else{
      APInt UB_LandMark(Rng->getWidth(), *ub_It, Rng->IsSigned());
      ub = UB_LandMark;
    }
  }

  DEBUG(dbgs() << "Widen interval based on landmarks: " 
	<< "widen([" << Rng->getLB() << "," << Rng->getUB() << "]) ="
	<< "[" << lb << "," << ub << "]\n");
}
#endif /* end widenOneInterval */

void wideningJump(Range *Old, Range * New, 
		  const std::vector<int64_t> &JumpSet,
		  APInt &lb, APInt &ub){

  APInt a = Old-> getLB();
  APInt b = Old-> getUB();
  APInt c = New-> getLB();
  APInt d = New-> getUB();

  // 1st case: neither of the two extremes stabilize
  if (Old->lessOrEqual(New) && (a!=c) && (b!=d)){
    widenOneInterval(New, JumpSet, lb, ub);
    return;
  }
  Range Merged(*Old);
  Merged.join(New);  
  // 2nd case: the upper bound does not stablize but the lower does
  if ( (Merged.getLB() == a) && (Merged.getUB() == d)){
    APInt lb_;
    lb = New->getLB();
    widenOneInterval(New, JumpSet, lb_, ub);
    return;
  }
  // 3rd case: the lower bound does not stabilize but the upper does
  if ( (Merged.getLB() == c) && (Merged.getUB() == b)){
    APInt ub_;
    ub = New->getUB();
    widenOneInterval(New, JumpSet, lb, ub_);
    return;
  }
  llvm_unreachable("Unsupported case");
}


/// Wrapper to call different widening methods.
void Range::widening(AbstractValue *PreviousV, 
		     const std::vector<int64_t> &JumpSet){

  switch(WideningMethod){
  case NOWIDEN:
    return;
  case COUSOT76:
    assert(PreviousV != NULL);
    wideningCousot77(cast<Range>(PreviousV),this);
    DEBUG(dbgs() << "\tWIDENING (Cousot77) has been applied:" << *this << "\n" );
    return;
  case JUMPSET:
    {
      APInt widenLB, widenUB;
      wideningJump(cast<Range>(PreviousV), this, JumpSet, widenLB, widenUB);
      // Normalization to top.
      if (IsSigned() &&
	  (widenLB == APInt::getSignedMinValue(getWidth()) ||
	   widenUB == APInt::getSignedMaxValue(getWidth()))){
	makeTop();
	goto END;
      }      
      if ((!IsSigned()) && 
	  (widenLB == APInt::getMinValue(getWidth()) ||
	   widenUB == APInt::getMaxValue(getWidth()))){
	makeTop();  
	goto END;
      }      
      setLB(widenLB);
      setUB(widenUB);
    END:
      CheckIntervalIsWellFormed(this, "WIDENING");
      DEBUG(dbgs() << "\tWIDENING (based on jumps) has been applied:" 
	           << *this << "\n");
    }
    return;
  default:
    llvm_unreachable("ERROR: widening method not implemented");
  }
}
  
// These operations are used to determine if the evaluation of a guard
// is true or not. Note that these do not change the abstract value of
// the variable involved in the guard. This will be done by
// propagateSigmaVarConst and propagateSigmaTwoVars.

bool Range::comparisonSle(AbstractValue *V){
  // if false then it's definite false if true then we still need to
  // check the negation of the condition. If also true, then
  // top. Otherwise, definite true.

  Range * I1 = this;
  Range * I2 = cast<Range>(V);
  // [a,b] <= [c,d] if a <= d
  return I1->getLB().sle(I2->getUB());
}


bool Range::comparisonSlt(AbstractValue *V){				 
  // if false then it's definite false if true then we still need to
  // check the negation of the condition. If also true, then
  // top. Otherwise, definite true.

  Range * I1 = this;
  Range * I2 = cast<Range>(V);
  APInt a = I1->getLB();
  APInt b = I1->getUB();
  APInt c = I2->getLB();
  APInt d = I2->getUB();

  // [a,b] < [c,d]  if a < d 
  return a.slt(d);
}

////////////////////////////////////////////////////


/// If IsStrict=true then <= else <
bool Range::comparisonUnsignedLessThan(Range *I1, Range *I2, bool IsStrict){

  // We need to cut at the south pole. Otherwise, queries like
  // [MININT, 3] <=_u [3,3] returns false, which is incorrect!

  std::vector<RangePtr> s1 = 
    ssplit(I1->getLB(), I1->getUB(), I1->getLB().getBitWidth(), true);
  std::vector<RangePtr> s2 = 
    ssplit(I2->getLB(), I2->getUB(), I2->getLB().getBitWidth(), true);
	   
  bool tmp=false;
  typedef std::vector<RangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      if (IsStrict)
	tmp |= comparisonUltDoNotCrossSP((*I1).get()->getLB(), 
					 (*I1).get()->getUB(), 
					 (*I2).get()->getLB(),
					 (*I2).get()->getUB());
      else
	tmp |= comparisonUleDoNotCrossSP((*I1).get()->getLB(),
					 (*I1).get()->getUB(),					 
					 (*I2).get()->getLB(),
					 (*I2).get()->getUB());
      if (tmp) return true; 
    }    
  }
  return tmp;
}

bool Range::comparisonUle(AbstractValue *V){
  Range * I1 = this;
  Range * I2 = cast<Range>(V);
  return comparisonUnsignedLessThan(I1,I2, false);
}

bool Range::comparisonUlt(AbstractValue *V){				 
  Range * I1 = this;
  Range * I2 = cast<Range>(V);
  return comparisonUnsignedLessThan(I1,I2, false);
}
////////////////////////////////////////////////////


/// Refine the intervals of the variables V1 and V2 involved in a
/// guard once we know if the evaluation of the guard is true or
/// false.
void Range::filterSigma(unsigned Pred,  AbstractValue *V1, AbstractValue *V2){
  Range *Var1   = cast<Range>(V1);
  Range *Var2   = cast<Range>(V2);

  if (!Var1->isConstant() && Var2->isConstant()){
    assert(Var2->IsConstantRange() 
	   && "Some inconsistency found in filterSigma");
    filterSigma_VarAndConst(Pred, Var1, Var2);    			      
  } 
  else if (!Var1->isConstant() &&  !Var2->isConstant()){
      filterSigma_TwoVars(Pred, Var1, Var2);
  }
  else
    llvm_unreachable("Unexpected case in filterSigma");

}

/// Case when one is variable and the other a constant in the branch
/// condition. V is the interval associated with the variable and N is
/// the interval associated with the constant.
void Range::filterSigma_VarAndConst(unsigned Pred, Range *V, Range *N){
  // Assumption: V is the range we would like to improve using     
  // information from Pred and N                                   
  Range *LHS = this;
  assert((!V->isConstant() && N->isConstant()) &&  (N->IsConstantRange()));

  switch (Pred){
  case ICmpInst::ICMP_EQ:
    { /* if v == n then [n,n] */       
      LHS->setLB(N->getLB());
      LHS->setUB(N->getUB());    
      return;
    }
  case ICmpInst::ICMP_NE:
    {
      // The only case to improve the range of V is in case N is
      // either the upper bound of V or its lower bound.  (Overflow is
      // not possible here. Assume overflow is possible, then the only
      // possibility of overflow would be if V=N=[MIN,MIN] and
      // V=N=[MAX,MAX]. But V cannot be equal to N)

      if (V->getLB() == N->getLB())
	LHS->setLB(V->getLB() + 1);      
      else
	LHS->setLB(V->getLB());

      if (V->getUB() == N->getUB())
	LHS->setUB(V->getUB() - 1);
      else
	LHS->setUB(V->getUB());          

      // tricky normalization step: if LHS is not improved and the
      // original value V was top then LHS must be kept as top.
      if (LHS->getLB() == V->getLB() && LHS->getUB() == V->getUB() && V->IsTop())
	LHS->makeTop();

      return;
    }
  case ICmpInst::ICMP_ULE:
  case ICmpInst::ICMP_SLE:
    { /* if v <= n then rng(v) /\ [-oo,n] */
      // prepare the range [-oo,n]
      Range TmpRng(*N);
      TmpRng.setLB(getMinValue(Pred));
      LHS->meet(V,&TmpRng);
      if (LHS->isBot()){
	// It's possible that V is less than N, and V and N are
	// disjoint. In that case, we return the range of V.
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }
  case ICmpInst::ICMP_ULT:	  
  case ICmpInst::ICMP_SLT:	  
    { /* if v < n then rng(v) /\ [-oo,n-1] */
      // prepate the range [-oo,n-1]

      Range TmpRng(*N);      
      TmpRng.setLB(getMinValue(Pred));
      // make sure we cannot have an overflow!
      // this method checks if it's signed or not
      // if (N->getLB() == N->getMinValue()) 
      // 	TmpRng.setUB(N->getLB());   
      // else
      TmpRng.setUB(N->getLB() - 1);         
      LHS->meet(V,&TmpRng);
      if (LHS->isBot()){
	// It's possible that V is less than N, and V and N are
	// disjoint. In that case, we return the range of V.
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }
  case ICmpInst::ICMP_UGT:
  case ICmpInst::ICMP_SGT:
    { /* if v > n then  rng(v) /\ [n+1,+oo] */ 
      // prepare range [n+1,+oo]
      Range TmpRng(*N);
      TmpRng.setUB(getMaxValue(Pred));
      // make sure we cannot have an overflow!
      // this method checks if it's signed or not
      // if (N->getUB() == N->getMaxValue()) 
      // 	TmpRng.setLB(N->getUB()); 
      // else
      TmpRng.setLB(N->getUB() + 1);       
      LHS->meet(V,&TmpRng);
      if (LHS->isBot()){
	// It's possible that V is greater than N, and V and N are
	// disjoint. In that case, we return the range of V
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }    
  case ICmpInst::ICMP_UGE:
  case ICmpInst::ICMP_SGE:
    { /* if v >= n then  rng(v) /\ [n,+oo] */ 
      // prepare the range [n,+oo]
      Range TmpRng(*N);
      TmpRng.setUB(getMaxValue(Pred));
      TmpRng.setLB(N->getUB()); 		    		  
      LHS->meet(V,&TmpRng);
      if (LHS->isBot()){
	// It's possible that V is greater than N, and V and N are
	// disjoint. In that case, we return the range of V.
	LHS->setLB(V->getLB());
	LHS->setUB(V->getUB());
      }
      return;
    }  
  default:
    llvm_unreachable("Unexpected error in filterSigma_VarAndConst");
  }
}

/// The condition of the branch involves two variables.
void Range::filterSigma_TwoVars(unsigned Pred, Range *I1, Range *I2){
  // Assumption: I1 is the range we would like to improve using
  // information from Pred and I2
  Range *LHS = this;
  assert(!I1->isConstant() &&  !I2->isConstant());
  assert((I1->IsSigned()   == I2->IsSigned()) &&
	 "Arguments must have same signedeness");

  // Special cases first
  if (I1->IsTop() && I2->IsTop()){
    LHS->makeTop();
    return;
  }

  if (I2->isBot() || I2->IsTop()){ 
    // If I2 is bottom or top, we dont' have chance to improve I1
    // FIXME: probably I1 should be bottom if I2 is bottom.
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  }

  LHS->meet(I1,I2);

  if (LHS->isBot()){
    // If I1 and I2 are disjoint we don't have chance to improve I1
    // E.g. [0,2] < [10,50]
    // The meet here is bottom so we cannot improve
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    return;
  }

  switch(Pred){
  case ICmpInst::ICMP_EQ: 
    // LHS is the meet between I1 and I2
    return;
  case ICmpInst::ICMP_NE:  
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());        
    // Minor improvement if I2 is a point
    if (I2->getLB() == I2->getUB()){ 
      if (I1->getLB() == I2->getLB())
    	LHS->setLB(LHS->getLB()+1);
      if (I1->getUB() == I2->getUB())
    	LHS->setUB(LHS->getUB()-1);
    }
    return;
  case ICmpInst::ICMP_ULT: // I1 <  I2
  case ICmpInst::ICMP_ULE: // I1 <= I2
  case ICmpInst::ICMP_SLT: // I1 <  I2
  case ICmpInst::ICMP_SLE: // I1 <= I2
    {
      bool IsSignedOp = (Pred == ICmpInst::ICMP_SLT || Pred == ICmpInst::ICMP_SLE);
      Range tmp1 = convertTopToNumInterval(I1,IsSignedOp);
      APInt a = tmp1.getLB();
      APInt b = tmp1.getUB();
      APInt c = I2->getLB();
      APInt d = I2->getUB();

      APInt refined_d;
      if (Pred == ICmpInst::ICMP_SLT || Pred == ICmpInst::ICMP_ULT)
	refined_d = d - 1;
      else 
	refined_d = d;

      LHS->setLB(a);
      bool canRefine;
      (IsSignedOp? canRefine = d.sle(b) : canRefine = d.ule(b));
      if (canRefine)
	LHS->setUB(refined_d);
      else
	LHS->setUB(b);
    }
    return;
    // if (I1->IsTop() || BaseRange::bridge_IsIncluded(Pred,
    // 				     I2->getLB(),I2->getUB(),
    // 				     I1->getLB(),I1->getUB())){
    //   // Case where we can improve further the meet: I2 is included in
    //   // I1
    //   // E.g., [-10,+oo] <= [-5,-2] --> [-10,-2]
    //   // E.g., [-10,+oo] <  [-5,-2] --> [-10,-3]
    //   LHS->setLB(I1->getLB());
    //   if (Pred == ICmpInst::ICMP_SLT || Pred == ICmpInst::ICMP_ULT)
    // 	LHS->setUB(I2->getUB() - 1);
    //   else
    // 	LHS->setUB(I2->getUB());
    //   return;
    // }
    // if (BaseRange::bridge_IsOverlapLeft(Pred,
    // 					I1->getLB(),I1->getUB(),
    // 					I2->getLB(),I2->getUB())){
    //   // The result is the meet between I1 and I2
    //   return;
    // }     
    // // Otherwise, no improvement. That is, overlap-right or I1 included
    // // in I2 cannot improve our knowledge about I1
    // LHS->setLB(I1->getLB());
    // LHS->setUB(I1->getUB());    
    // return;
  case ICmpInst::ICMP_UGT: 
  case ICmpInst::ICMP_UGE: 
  case ICmpInst::ICMP_SGT: 
  case ICmpInst::ICMP_SGE: 
    {
      bool IsSignedOp = (Pred == ICmpInst::ICMP_SGE || Pred == ICmpInst::ICMP_SGT);
      Range tmp1 = convertTopToNumInterval(I1,IsSignedOp);
      APInt a = tmp1.getLB();
      APInt b = tmp1.getUB();
      APInt c = I2->getLB();
      APInt d = I2->getUB();

      APInt refined_c;
      if (Pred == ICmpInst::ICMP_SGE || Pred == ICmpInst::ICMP_UGE)
	refined_c= c;
      else 
	refined_c = c+1;

      LHS->setUB(b);
      bool canRefine;
      (IsSignedOp? canRefine = a.sle(c) : canRefine = a.ule(c));
      if (canRefine)
	LHS->setLB(refined_c);
      else
	LHS->setLB(a);
    }
    return;
    // if (BaseRange::bridge_IsIncluded(Pred,
    // 				     I2->getLB(),I2->getUB(),
    // 				     I1->getLB(),I1->getUB())){
    //   // Case where we can improve further the meet:
    //   // E.g., [-10,+oo] >= [-5,-2] --> [-5,+oo]
    //   // E.g., [-10,+oo] >  [-5,-2] --> [-4,+oo]
    //   LHS->setUB(I1->getUB());
    //   if (Pred == ICmpInst::ICMP_SGE || Pred == ICmpInst::ICMP_UGE)
    // 	LHS->setLB(I2->getLB());
    //   else
    // 	LHS->setLB(I2->getLB()+1);	
    //   return;
    // }
    // if (BaseRange::bridge_IsOverlapRight(Pred,
    // 					 I1->getLB(),I1->getUB(),
    // 					 I2->getLB(),I2->getUB())){
    //   // The result is the meet between I1 and I2
    //   return;
    // }
    // // Otherwise, no improvement. That is, overlap-left or if I1 is
    // // included in I2 do not provide new knowledge about I1
    // LHS->setLB(I1->getLB());
    // LHS->setUB(I1->getUB());    
    // return;
  default: ;
  }
}


/// Compute the transfer function for arithmetic binary operators and
/// check for overflow. If overflow detected then top.
AbstractValue* Range::
visitArithBinaryOp(AbstractValue* V1, AbstractValue* V2,
		   unsigned OpCode, const char * OpCodeName ){
  
  Range *Op1 = cast<Range>(V1);
  Range *Op2 = cast<Range>(V2);
  Range *LHS = new Range(*this);

  DEBUG(dbgs() << "\t[RESULT] " 
	<< *Op1 << " " << OpCodeName << " " << *Op2 << " = ");
  
  bool IsOverflow;
  DoArithBinaryOp(LHS,Op1,Op2,OpCode,OpCodeName,IsOverflow);
  // Most arithmetic operations can raise overflow except unsigned
  // division and unsigned rem.
  if (IsOverflow) {
    LHS->makeTop();
    NumOfOverflows++;
  }

#ifdef CHECK_WELLFORMED 
  CheckIntervalIsWellFormed(LHS,"DoArithBinaryOp");
#endif 

  DEBUG(dbgs()<< *LHS << "\n");   
  return LHS;
}

/// Execute an arithmetic operation but the caller will deal with
/// overflow.
///
/// OVERFLOW NOTES: We detect arithmetic overflows in a post-morten
/// way. That is, we rely on the APInt class which perform the
/// arithmetic operations and then set up a flag to report if an
/// overflow occurred during the operations.
void Range::DoArithBinaryOp(Range *LHS, Range *Op1, Range *Op2,
			    unsigned OpCode, const char *OpCodeName, 
			    bool &IsOverflow){
  // For debugging:
  // Instruction *I = cast<Instruction>(LHS->getValue());
  // dbgs() <<  *I  << "\n";

  IsOverflow = false;
  // First simple cases: bottom, top, etc.
  if (Op1->isBot() || Op2->isBot()){
    LHS->makeBot();
    return;
  }
  if (Op1->IsTop() || Op2->IsTop()){
    LHS->makeTop();
    return;
  }
  assert(Op1->IsSigned() == Op2->IsSigned() &&
	 "Arguments must have same signedeness");

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();

  switch (OpCode){
  case Instruction::Add:
    {
      /// [a,b] + [c,d] = [a+c,b+d]
      bool OverflowLB,OverflowUB;
      if (Op1->IsSigned()){ 
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.sadd_ov(Op2->getLB(),OverflowLB));
	LHS->setUB(Op1->getUB());           
	LHS->setUB(LHS->UB.sadd_ov(Op2->getUB(),OverflowUB));
      }
      else{
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.uadd_ov(Op2->getLB(),OverflowLB));
	LHS->setUB(Op1->getUB());           
	LHS->setUB(LHS->UB.uadd_ov(Op2->getUB(),OverflowUB));
      }
      IsOverflow = (OverflowLB || OverflowUB);
      /* debugging info */
      if (IsOverflow){
	if (Op1->IsSigned()) DEBUG(dbgs() << " (signed overflow)");
	else                 DEBUG(dbgs() << " (unsigned overflow)");
      }

    }
    break;
  case Instruction::Sub:
    {
      // [a,b] - [c,d] = [a-d, b-c]
      bool OverflowLB,OverflowUB;
      if (Op1->IsSigned()){
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.ssub_ov(Op2->getUB(),OverflowLB));
	LHS->setUB(Op1->getUB());
	LHS->setUB(LHS->UB.ssub_ov(Op2->getLB(),OverflowUB));
      }
      else{
	LHS->setLB(Op1->getLB());
	LHS->setLB(LHS->LB.usub_ov(Op2->getUB(),OverflowLB));
	LHS->setUB(Op1->getUB());
	LHS->setUB(LHS->UB.usub_ov(Op2->getLB(),OverflowUB));
      }
      IsOverflow = (OverflowLB || OverflowUB);
      /* debugging info */      
      if (IsOverflow){
	if (Op1->IsSigned()) DEBUG(dbgs() << "(signed overflow) ");
	else                 DEBUG(dbgs() << "(unsigned overflow) ");
      }
    }
    break;
  case Instruction::Mul:
    {      
      if (Op1->IsZeroRange())
	LHS->RangeAssign(Op1);
      else if (Op2->IsZeroRange())
	LHS->RangeAssign(Op2);
      else
	DoMultiplication(Op1->IsSigned(), LHS, Op1, Op2, IsOverflow);
    }
    break;
  case Instruction::UDiv:
  case Instruction::SDiv:
    {
      if (Op2->IsZeroRange()){
	LHS->makeBot();
      }
      else if (Op1->IsZeroRange())
	LHS->RangeAssign(Op1);
      else
	DoDivision((OpCode == Instruction::SDiv) ? true : false,
		   LHS,Op1,Op2,IsOverflow);
    }
    break;
  case Instruction::URem:
  case Instruction::SRem:
    {
      if (Op2->IsZeroRange())
	LHS->makeBot();
      else if (Op1->IsZeroRange())
	LHS->RangeAssign(Op1);
      else
	DoRem((OpCode == Instruction::SRem) ? true : false,
	      LHS,Op1,Op2,IsOverflow);
    }
    break;
  default:
    dbgs() << OpCodeName << "\n";
    llvm_unreachable("Arithmetic operation not implemented");
  } // end switch
}

/// [a,b] * [c,d] = [min(a*c,a*d,b*c,b*d),max(a*c,a*d,b*c,b*d)].
void Range:: DoMultiplication(bool IsSignedOp,
			      Range *LHS, Range *Op1, Range *Op2,
			      bool &IsOverflow){
  APInt a,b,c,d;
  bool Overflow1,Overflow2,Overflow3,Overflow4;
  // FIXME: Do multiplications and overflow checks lazily
  if (IsSignedOp){
    a = Op1->getLB().smul_ov(Op2->getLB(),Overflow1);
    b = Op1->getLB().smul_ov(Op2->getUB(),Overflow2);
    c = Op1->getUB().smul_ov(Op2->getLB(),Overflow3);
    d = Op1->getUB().smul_ov(Op2->getUB(),Overflow4);
  }
  else{
    a = Op1->getLB().umul_ov(Op2->getLB(),Overflow1);
    b = Op1->getLB().umul_ov(Op2->getUB(),Overflow2);
    c = Op1->getUB().umul_ov(Op2->getLB(),Overflow3);
    d = Op1->getUB().umul_ov(Op2->getUB(),Overflow4);    
  }
  // FIXME: for simplicity if one of the above multiplications arises
  // overflow, we return overflow:
  IsOverflow = (Overflow1 || Overflow2 || Overflow3 || Overflow4);	
  // FIXME: if overflow arises then the below code may be useless
  // (e.g., for RangeLattice instances)
  if (IsSignedOp){
    LHS->setLB(smin(smin(smin(a,b),c),d));
    LHS->setUB(smax(smax(smax(a,b),c),d));
  }
  else{
    LHS->setLB(umin(umin(umin(a,b),c),d));
    LHS->setUB(umax(umax(umax(a,b),c),d));    
  }
  /* debugging info */      
  if (IsOverflow){
    if (IsSignedOp)
      DEBUG(dbgs() << "(signed overflow) ");  
    else
      DEBUG(dbgs() << "(unsigned overflow) ");	  
  }
}

/// Auxiliary method to remove [0,0]. 
/// pre: [a,b] != [0,0]
/// if [0,b]           then { [1,b]  } where b > 0
/// if [a,0]           then { [a,-1] } where a < 0
/// if [0,0] \in [a,b] then { [a,-1], [1, b] }
/// else                    { [a,b] }
std::vector<RangePtr> 
purgeZero(const APInt &x, const APInt &y, unsigned width, bool IsSignedOp){
  assert( !(x == 0  && y == 0) && "Interval cannot be [0,0]");

  bool IsSigned=true;
  // Temporary wrapped interval for zero
  APInt Zero_lb(width, 0, IsSigned);          // 000...0 
  APInt Zero_ub(width, 0, IsSigned);          // 000...0 
  Range Zero(Zero_lb,Zero_ub,width,IsSigned);
  // Temporary wrapped interval 
  RangePtr s(new Range(x, y, width, IsSigned));
  std::vector<RangePtr> res;
  if (Zero.lessOrEqual(s.get())){
    if (x == 0 ){
      assert( (y.isStrictlyPositive())  && "Upper bound must be greater than 0");
      // Does not cross the south pole
      RangePtr s(new Range(x+1,y,width,IsSigned)); 
      res.push_back(s);      
    }
    else{
      if (y == 0){
	assert(x.isNegative() && "Lower bound must be smaller than 0");
	// If interval is e.g., [1000,0000] then we keep one interval
	APInt minusOne = APInt::getMaxValue(width); // 111...1
	RangePtr s(new Range(x,minusOne,width,IsSigned)); // [x, 111....1]
	res.push_back(s);	
      }
      else{
	// General case: split into two intervals
	APInt plusOne(width, 1, IsSigned);          // 000...1 
	APInt minusOne = APInt::getMaxValue(width); // 111...1
	RangePtr s1(new Range(x,minusOne,width,IsSigned)); // [x, 111....1]
	RangePtr s2(new Range(plusOne,y,width,IsSigned)); // [000...1,  y] 
	res.push_back(s1);
	res.push_back(s2);
      }
    }
  }
  else    
    res.push_back(s); // No need of split

  return res;
}

inline bool APINT_SIGNED_LESS(const APInt &a, const APInt &b){
  return a.slt(b);
}
    
inline bool APINT_UNSIGNED_LESS(const APInt &a, const APInt &b){
  return a.ult(b);
}

/// Pre: Divisor is not the singleton [0,0]
void Range::DoDivision(bool IsSignedOp,
		       Range *LHS, Range *Dividend, Range *Divisor,
		       bool &IsOverflow){

  IsOverflow=false; // by default no overflow

  // We remove the interval [0,0] from Divisor
  std::vector<RangePtr> s1 = 
    purgeZero(Divisor->getLB(), Divisor->getUB(), 
	      Divisor->getLB().getBitWidth(), IsSignedOp);

  // dbgs() << "Divisor " << *Divisor << " split into : " << s1 << "\n";

  APInt a = Dividend->getLB();
  APInt b = Dividend->getUB();

  std::vector<APInt> extremes;
  for (std::vector<RangePtr>::iterator Divisors = s1.begin(), 
	 E1 =s1.end(); Divisors != E1; ++Divisors){
    APInt c = (*Divisors).get()->getLB();
    APInt d = (*Divisors).get()->getUB();

    if (IsSignedOp){
      APInt e1 = a.sdiv_ov(c,IsOverflow);
      if (IsOverflow){
	DEBUG(dbgs() << "(signed division overflow) ");
	return;
      }
      extremes.push_back(e1);
      APInt e2 = a.sdiv_ov(d,IsOverflow);
      if (IsOverflow){
	DEBUG(dbgs() << "(signed division overflow) ");
	return;
      }
      extremes.push_back(e2);
      APInt e3 = b.sdiv_ov(c,IsOverflow);
      if (IsOverflow){
	DEBUG(dbgs() << "(signed division overflow) ");
	return;
      }
      extremes.push_back(e3);
      APInt e4 = b.sdiv_ov(d,IsOverflow);
      if (IsOverflow){
	DEBUG(dbgs() << "(signed division overflow) ");
	return;
      }
      extremes.push_back(e4);
    }
    else{
      extremes.push_back(a.udiv(c));
      extremes.push_back(a.udiv(d));
      extremes.push_back(b.udiv(c));
      extremes.push_back(b.udiv(d));
    }
  }

  // We force signed view even if the operation is unsigned.
  // Otherwise, we can get bad formed intervals.
  IsSignedOp=true;
  LHS->setLB(*std::min_element(extremes.begin(), extremes.end(), 
			       (IsSignedOp ? APINT_SIGNED_LESS: APINT_UNSIGNED_LESS)));
  LHS->setUB(*std::max_element(extremes.begin(), extremes.end(), 
			       (IsSignedOp ? APINT_SIGNED_LESS: APINT_UNSIGNED_LESS)));
  return;
}

/// Both SRem and URem are irregular in the sense that it is not sound
/// to look only at the endpoints. E.g., urem([3,7],[4,5]) = [2,3] if
/// we try only the endpoints. However, 0,1, and 4 are also possible
/// remainders.
///
/// Given a dividend a and divisor b a remainder always satisfies the
/// condition: a/b * b + rem = a
///
/// Divisor is not the singleton [0,0]
///
/// SRem can produce overflow if MININT urem -1.
///
void DoRemCases(const APInt &a, const APInt &b, const APInt &c, const APInt &d, 
		unsigned width, bool IsSigned,
		APInt &lb, APInt &ub){
  
  unsigned char case_val = 0;
  case_val += (a.isNonNegative() ? 1 : 0);
  case_val <<= 1;
  case_val += (b.isNonNegative() ? 1 : 0);
  case_val <<= 1;
  case_val += (c.isNonNegative() ? 1 : 0);
  case_val <<= 1;
  case_val += (d.isNonNegative() ? 1 : 0);

  switch (case_val) {
  case 0: // - - - - 
    lb = c+1;
    ub = APInt(width, 0, IsSigned); 
    break;
  // case 1: // - - - +
  //   lb = 
  //   ub = 
  //   break;
  case 3: // - - + +
    lb = -d+1;
    ub = APInt(width, 0, IsSigned); 
    break;
  case 4: // - + - - 
    lb = c+1;
    ub = -c-1;
    break;
  // case 5: // - + - + 
  //   lb = 
  //   ub = 	
  //   break;
  case 7: // - + + + 
    lb = -d+1;
    ub =  d-1;
    break;
  case 12: // + + - - 
    lb = APInt(width, 0, IsSigned); 
    ub = -c-1;
    break;
  // case 13: // + + - + 
  //   lb =
  //   ub =
  //   break; 
  case 15: // + + + + 
    lb = APInt(width, 0, IsSigned); 
    ub = d-1;
    break;
  default:
    {
      dbgs() << "[" << a << "," << b << "]" << " % " << "[" << c << "," << d << "]\n" ;
      llvm_unreachable("SRem: case not implemented");
    }
  }
  return;
}


void Range::DoRem(bool IsSignedOp,
		  Range *LHS, Range *Dividend, Range *Divisor,
		  bool &IsOverflow){

  IsOverflow=false; // by default no overflow
  // FIXME: we are not checking the rare case of overflow if MININT
  // SRem -1.

  std::vector<RangePtr> s1 = 
    purgeZero(Divisor->getLB(), Divisor->getUB(), 
	      Divisor->getLB().getBitWidth(), IsSignedOp);

  APInt a = Dividend->getLB();
  APInt b = Dividend->getUB();
   
  std::vector<APInt> extremes;
  for (std::vector<RangePtr>::iterator Divisors = s1.begin(), E1 =s1.end(); 
       Divisors != E1; ++Divisors){
    APInt c = (*Divisors).get()->getLB();
    APInt d = (*Divisors).get()->getUB();
    APInt lb, ub;
    DoRemCases(a,b,c,d,width,IsSignedOp,lb,ub);
    extremes.push_back(lb);
    extremes.push_back(ub);
  }

  // We force signed view even if the operation is unsigned.
  // Otherwise, we can get bad formed intervals.
  IsSignedOp=true;
  LHS->setLB(*std::min_element(extremes.begin(), extremes.end(), 
			       (IsSignedOp ? APINT_SIGNED_LESS: APINT_UNSIGNED_LESS)));
  LHS->setUB(*std::max_element(extremes.begin(), extremes.end(), 
			       (IsSignedOp ? APINT_SIGNED_LESS: APINT_UNSIGNED_LESS)));

}

/// Perform the transfer function for casting operations and check
/// overflow. If overflow detected then top.
AbstractValue * Range::
visitCast(Instruction &I,  AbstractValue * V, TBool * TB, bool IsSigned){

  Range *RHS = NULL;    
  if (!V){
    // Special case if the source is a Boolean Flag    
    assert(TB && "ERROR: visitCat assumes that TB != NULL");
    RHS = new Range(I.getOperand(0), TB, IsSigned); 
  }
  else{
    // Common case
    RHS = cast<Range>(V);    
    assert(!TB && "ERROR: some inconsistency found in visitCast");
  }

  Range *LHS = new Range(*this);
  bool IsOverflow;
  DoCast(LHS,RHS,I.getOperand(0)->getType(),I.getType(),I.getOpcode(),IsOverflow);

  if (!V) delete RHS;

  // note that only Trunc (truncation) can raise overflow
  if (IsOverflow){
    LHS->makeTop(); 
    NumOfOverflows++;
  }

  DEBUG(dbgs() << "\t[RESULT]");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");      
  return LHS;

}

/// Return true iff overflow during the truncate
/// operations. Overflow can happen if the interval does not fit into an
/// integer of destWidth bits.
bool Range::IsTruncateOverflow(Range * RHS, unsigned destWidth){
  // Note: overflow can happen both if the integer is signed or
  // unsigned. E.g. if the unsigned interval [000111,011011] is
  // truncated to 3 bits we would get [111,011] which is
  // wrapped. Therefore, we should return overflow since 0111011 does
  // not fit into 3 bits. (remember BaseRange assumes that
  // intervals cannot wraparound)

  // If LB is -oo or UB +oo then there is no overflow
  if (RHS->IsSigned()){
    return (((RHS->getUB().sgt(APInt::getSignedMaxValue(destWidth).getSExtValue()))) ||
	    ((RHS->getLB().slt(APInt::getSignedMinValue(destWidth).getSExtValue()))));
  }
  else{
    return (((RHS->getUB().ugt(APInt::getMaxValue(destWidth).getZExtValue()))) ||
	    ((RHS->getLB().ult(APInt::getMinValue(destWidth).getZExtValue()))));
  }  
}

/// Perform casting operations. The caller is in charge for handling
/// overflow.
void Range::
DoCast(Range *LHS, Range *RHS, 
       const Type *srcTy, const Type *destTy, 
       const unsigned OpCode, bool &IsOverflow){
  IsOverflow=false;

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();

  unsigned srcWidth,destWidth;  
  assert(LHS->IsSigned() == RHS->IsSigned() &&
	 "Arguments must have same signedeness");

  BaseRange::
    checkCastingOp(srcTy,srcWidth,destTy,destWidth,OpCode,RHS->getWidth());
  
  //  Perform casting                             
  LHS->setZeroAndChangeWidth(destWidth);        
  // gross fix: RHS is actually top but IsTop does not detect it
  RHS->normalizeTop();  

  // Simple cases first: bottom and top
  if (RHS->isBot())
    LHS->makeTop(); // be conservative
  else if (RHS->IsTop()){
    LHS->makeTop();
    IsOverflow=false;
  }
  else{
    switch(OpCode) {
    case Instruction::Trunc:
      if (IsTruncateOverflow(RHS,destWidth)){
	DEBUG(dbgs() << "\tCast: truncating an integer that does not fit in the destination " 
	      << destWidth << " bits.\n");	
	IsOverflow=true;
      }
      else{
	IsOverflow=false;
	LHS->setUB(RHS->getUB().trunc(destWidth)); 
	LHS->setLB(RHS->getLB().trunc(destWidth)); 	  
#ifdef DEBUG_CAST_OP
	dbgs() << "Trunc(";
	RHS->printRange(dbgs());
	dbgs() << "," << destWidth << ")=";
	RHS->printRange(dbgs());
	dbgs() << "\n";
#endif 
      }
      break;
    case Instruction::SExt:
      //// If we force a signed view (default) then we cannot cross the
      //// north pole
      //// 
      // if (isCrossingNorthPole(RHS)){
      //   // dbgs() << "Crossing north pole!\n";
      //   // If the interval crosses the north pole then we go to top
      //   // using srcWidth's and then we signed extend to destWidth
      //   LHS->setLB(APInt::getSignedMinValue(srcWidth).sext(destWidth));
      //   LHS->setUB(APInt::getSignedMaxValue(srcWidth).sext(destWidth));
      // }
      // else{
      // Apply sext
      LHS->setLB(RHS->getLB().sext(destWidth));
      LHS->setUB(RHS->getUB().sext(destWidth));    
      // }
#ifdef DEBUG_CAST_OP
      dbgs() << "SExt(";
      RHS->printRange(dbgs());
      dbgs() << "," << destWidth << ")=";
      RHS->printRange(dbgs());
      dbgs() << "\n";
#endif 
      break;
    case Instruction::ZExt:
      /// If we force a signed view (default) then we can cross the
      /// south pole.
      if (isCrossingSouthPole(RHS)){
	// If the interval crosses the south pole then we go to top
	// using srcWidth's and then we unsigned extend to destWidth
	LHS->setLB(APInt::getNullValue(srcWidth).zext(destWidth));
	LHS->setUB(APInt::getMaxValue(srcWidth).zext(destWidth));
      }
      else{
	// Apply zext 
	LHS->setLB(RHS->getLB().zext(destWidth));
	LHS->setUB(RHS->getUB().zext(destWidth));    
      }
#ifdef DEBUG_CAST_OP
      dbgs() << "ZExt(";
      RHS->printRange(dbgs());
      dbgs() << "," << destWidth << ")=";
      RHS->printRange(dbgs());
      dbgs() << "\n";
#endif 
      break;
    case Instruction::BitCast:
      assert(srcWidth == destWidth && 
	     "ERROR: violation of BitCast precondition");
      // Do nothing: assign rhs to lhs
      LHS->setLB(RHS->getLB());
      LHS->setUB(RHS->getUB());    
      break;
    default:
      llvm_unreachable("ERROR: unknown instruction in BasicCast");
    }  
  } 
#ifdef CHECK_WELLFORMED 
  CheckIntervalIsWellFormed(LHS,"DoCast");
#endif
}

/// Perform the transfer function for bitwise operations and check
/// overflow. If overflow detected then top.
AbstractValue * Range:: 
  visitBitwiseBinaryOp(AbstractValue * V1, AbstractValue * V2, 
		       const Type * Op1Ty, const Type * Op2Ty, 
		       unsigned OpCode,const char * OpCodeName){
  Range *Op1 = cast<Range>(V1);
  Range *Op2 = cast<Range>(V2);
  Range *LHS = new Range(*this);
  DEBUG(dbgs() << "\t[RESULT] ");
  DEBUG(Op1->printRange(dbgs())); 
  DEBUG(dbgs() << " " << OpCodeName << " ");
  DEBUG(Op2->printRange(dbgs())); 
  DEBUG(dbgs() << " = ");
  
  bool IsOverflow;
  DoBitwiseBinaryOp(LHS, Op1, Op2, Op1Ty, Op2Ty, OpCode, IsOverflow);
  // note that only Shl (left shift) can arise an overflow
  if (IsOverflow){  
    LHS->makeTop();
    NumOfOverflows++;
  }

#ifdef CHECK_WELLFORMED 
  CheckIntervalIsWellFormed(LHS,"DoBitwiseBinaryOp");
#endif

  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");        
  return LHS;  
}

/// Perform bitwise operations.  
void Range:: 
  DoBitwiseBinaryOp(Range * LHS, Range * Op1, Range * Op2, 
		    const Type * Op1Ty, const Type * Op2Ty, 
		    unsigned OpCode, bool &IsOverflow){	 
  
  assert(OpCode == Instruction::And  || OpCode == Instruction::LShr || 
	 OpCode == Instruction::Xor  || OpCode == Instruction::Shl ||
	 OpCode == Instruction::Or   || OpCode == Instruction::AShr );
  assert(Op1->IsSigned() == Op2->IsSigned() &&
	 "Arguments must have same signedeness");
  IsOverflow=false;
  // bottom and top are treated by callee methods

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();

  switch(OpCode){
  case Instruction::Shl:
  case Instruction::LShr:
  case Instruction::AShr:
    DoBitwiseShifts(LHS,Op1,Op2,OpCode,IsOverflow);
    break;
  case Instruction::Or:
  case Instruction::And:
  case Instruction::Xor:
    DoLogicalBitwise(LHS, Op1, Op2, OpCode);
    break;
  default: ;
  } // end switch  

}
   
void Range::
  DoBitwiseShifts(Range *LHS, Range *Operand, Range * Shift,
		  unsigned OpCode, bool &IsOverflow){
  
  // The shift is treated as an unsigned. This is part of the
  // semantics of the shl, lshr, and ashr.
  
  if (Operand->isBot() || Shift->isBot()){
    // be conservative here
    LHS->makeTop(); 
    return;
  }
  
  if (Shift->IsTop()){
    // this can happen often if shift is an input parameter and no
    // interprocedural analysis
    LHS->makeTop();
    return;
  }
  
  if (Shift->IsZeroRange()){
    // If the shift is zero then the instruction is a non-op
    LHS->RangeAssign(Operand);
   return;
  }
  
  // Temporary to check how often non-constant shifts
  // if (!Shift->IsConstantRange()){
  //   Shift->printRange(dbgs());
  //   assert( false && "ERROR: shift is not constant");
  // }
 
 if ( (!checkOpWithShift(Operand, Shift)) || (!Shift->IsConstantRange()) ){
   LHS->makeTop();
   return;
 }
 
  // Here the shift is constant
  APInt k        = Shift->getLB();

  IsOverflow =false;
  switch(OpCode){
  case Instruction::Shl:
    {
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();
      if (Operand->IsTop()){
	// The best thing we can hope for is top.  In wrapped
	// intervals we could get [0^{w},1^{w-k}0^{k}] but this
	// cannot be represented in classical fixed-width.
	LHS->makeTop();
      }
      else{
	bool IsOverflow1, IsOverflow2;
	LHS->setLB(a.sshl_ov((uint64_t) k.getZExtValue(), IsOverflow1));
	LHS->setUB(b.sshl_ov((uint64_t) k.getZExtValue(), IsOverflow2));
	IsOverflow = IsOverflow1 || IsOverflow2;       	
      }
    }
    break;
  case Instruction::LShr:
    {
      /// If we force signed view (default) then we can cross the
      /// south pole.
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();
      if (Operand->IsTop() || isCrossingSouthPole(Operand)){
	// 0^{w}
	LHS->setLB(APInt::getNullValue(a.getBitWidth()));
	// 0^{k}1^{w-k}
	LHS->setUB(APInt::getLowBitsSet(a.getBitWidth(), 
					a.getBitWidth() - k.getZExtValue())); 
	// more conservative:
	// LHS->makeTop();
      }
      else{
	LHS->setLB(a.lshr(k));
	LHS->setUB(b.lshr(k));
      }
      //      dbgs()<< "[" << LHS->getLB().toString(2,false) << "," 
      //	    << LHS->getUB().toString(2,false) << "]\n" ;
    }
    break;
  case Instruction::AShr:
    {
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();
      /// If we force signed view (default) then cannot cross the north pole.
      if (Operand->IsTop() /*|| isCrossingNorthPole(Operand)*/){
	// lower bound is 1...10....0 where the number of 1's is k.
	// if MSB=0 then [0^{w},0^{k}1^{w-k}]
	// if MSB=1 then [1^{k}0^{w-k},0^{w}]. Thus, by joining them 
	// 1^{k}0^{w-k}
	LHS->setLB(APInt::getHighBitsSet(a.getBitWidth(), k.getZExtValue()));  
	// 0^{k}1^{w-k}
	LHS->setUB(APInt::getLowBitsSet(b.getBitWidth(), 
					b.getBitWidth() - k.getZExtValue()));    

	// Important: if we force unsigned view this interval cannot
	// be represented so we need to go to top.
      }
      else{
	LHS->setLB(a.ashr(k));
	LHS->setUB(b.ashr(k));
      }
      //   dbgs()<< "[" << LHS->getLB().toString(2,false) << "," 
      //	 << LHS->getUB().toString(2,false) << "]\n" ;

    }
    break;
  default:
    llvm_unreachable("bitwise shift operation not implemented");
  }    
}


/// And, Or and Xor are irregular in the sense that it is not sound to
/// look only at the endpoints. We rely on the algorithms described in
/// Hacker's Delight book.
void Range::DoLogicalBitwise(Range *LHS, Range *Op1, Range *Op2,
			     unsigned Opcode){
  if (Op1->isBot() || Op2->isBot()){
    LHS->makeTop(); // be conservative here
    return;
  }

  if (Op1->IsTop() && Op2->IsTop()){
    LHS->makeTop();
    return;
  }
      
  switch (Opcode){
  case Instruction::Or:    
    {
      Range Tmp1 = convertTopToNumInterval(Op1, isSigned);
      Range Tmp2 = convertTopToNumInterval(Op2, isSigned);

      if (isSigned) 
	LHS->signedOr(&Tmp1,&Tmp2);
      else{          
	APInt lb; APInt ub;
	unimelb::unsignedOr(&Tmp1,&Tmp2,lb,ub);
	LHS->setLB(lb);
	LHS->setUB(ub);
      }
    }
    break;
  case Instruction::And:
    {
      Range Tmp1 = convertTopToNumInterval(Op1, isSigned);
      Range Tmp2 = convertTopToNumInterval(Op2, isSigned);

      if (isSigned) 
	LHS->signedAnd(&Tmp1,&Tmp2);
      else{          
	APInt lb; APInt ub;
	unimelb::unsignedAnd(&Tmp1,&Tmp2,lb,ub);
	LHS->setLB(lb);
	LHS->setUB(ub);
      }
    }
    break;
  case Instruction::Xor:
    {
      Range Tmp1 = convertTopToNumInterval(Op1, isSigned);
      Range Tmp2 = convertTopToNumInterval(Op2, isSigned);
      if (isSigned) 
	LHS->signedXor(&Tmp1,&Tmp2);
      else{          
	APInt lb; APInt ub;
	unimelb::unsignedXor(&Tmp1,&Tmp2,lb,ub);
	LHS->setLB(lb);
	LHS->setUB(ub);
      }
    }
    break;
  default:     
    llvm_unreachable("This should not happen");
  } // end switch  

  // Important normalization
  LHS->normalizeTop();
}

// Return true if S is crossing the south pole (i.e., from 111...1 to
// 000...0)
bool Range::isCrossingSouthPole(Range * S){
  unsigned width    = S->getWidth();
  unsigned isSigned = S->IsSigned();
  APInt SP_lb = APInt::getMaxValue(width); // 111...1
  APInt SP_ub(width, 0,isSigned);          // 000...0 
  Range SP(SP_lb,SP_ub,width,isSigned);
  return SP.lessOrEqual(S);
}

/// Signed bitwise or as described in Table 4.1 from Hacker's Delight
/// book.
void Range::signedOr(Range *Op1, Range*Op2){
  // We can alternatively define signedOr in the same way that we do
  // with signedAnd and signedXor.

  // Op1->printRange(dbgs());
  // dbgs() << " signedOR " ;
  // Op2->printRange(dbgs());
  // dbgs() << " = ";

  APInt a = Op1->getLB();   
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();   
  APInt d = Op2->getUB();   

  unsigned width = a.getBitWidth();

  unsigned char case_val = 0;
  case_val += (a.isNonNegative() ? 1 : 0);
  case_val <<= 1;
  case_val += (b.isNonNegative() ? 1 : 0);
  case_val <<= 1;
  case_val += (c.isNonNegative() ? 1 : 0);
  case_val <<= 1;
  case_val += (d.isNonNegative() ? 1 : 0);
  
  APInt lb, ub;
  switch (case_val) {
  case 0: // - - - - 
    lb = minOr(a, b, c, d);
    ub = maxOr(a, b, c, d);
    break;
  case 1: // - - - +
    lb = a;
    ub = APInt(width, -1, true);
    break;
  case 3: // - - + +
    lb = minOr(a, b, c, d);
    ub = maxOr(a, b, c, d);
    break;
  case 4: // - + - - 
    lb = c;
    ub = APInt(width, -1, true);
    break;
  case 5: // - + - + 
    lb = smin(a,c);
    ub = maxOr(APInt::getNullValue(width), b, 
	       APInt::getNullValue(width), d);
    break;
  case 7: // - + + + 
    lb = minOr(a, ~APInt::getNullValue(width), c, d);
    ub = maxOr(APInt::getNullValue(width), b, c, d);
    break;
  case 12: // + + - - 
    lb = minOr(a, b, c, d);
    ub = maxOr(a, b, c, d);
    break;
  case 13: // + + - + 
    lb = minOr(a, b, c, ~APInt::getNullValue(width) );
    ub = maxOr(a, b, APInt::getNullValue(width), d);
    break; 
  case 15: // + + + + 
    lb = minOr(a, b, c, d);
    ub = maxOr(a, b, c, d);
    break;
  default:
    dbgs() << "Uncovered case: " << case_val << "\n";
    llvm_unreachable("This should not happen");
  }  
  setLB(lb);
  setUB(ub);
  
  // this->printRange(dbgs());
  // dbgs() << "\n";
 }

void Range::signedAnd(Range *Op1, Range *Op2){
  bool IsSigned = true;
  // Cut at the south poles, apply unsigned AND on each pair of
  // intervals, and join them.
  std::vector<RangePtr> s1 = 
    ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), IsSigned);
  std::vector<RangePtr> s2 = 
    ssplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth(), IsSigned);

  this->makeBot();  
  for (std::vector<RangePtr>::iterator I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (std::vector<RangePtr>::iterator I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      APInt lb; APInt ub;
      unimelb::unsignedAnd((*I1).get(), (*I2).get(), lb, ub);
      Range tmp(lb,ub, Op1->getWidth(), Op1->IsSigned());  
      this->join(&tmp);
    }
  }
}

void Range::signedXor(Range *Op1, Range *Op2){
  bool IsSigned = true;
  // Cut at the south poles, apply unsigned AND on each pair of
  // intervals, and join them.
  std::vector<RangePtr> s1 = 
    ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), IsSigned);
  std::vector<RangePtr> s2 = 
    ssplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth(), IsSigned);

  this->makeBot();  
  for (std::vector<RangePtr>::iterator I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (std::vector<RangePtr>::iterator I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      APInt lb; APInt ub;
      unimelb::unsignedXor((*I1).get(),(*I2).get(),lb,ub);
      Range tmp(lb,ub, Op1->getWidth(), Op1->IsSigned());  
      this->join(&tmp);
    }
  }
}





