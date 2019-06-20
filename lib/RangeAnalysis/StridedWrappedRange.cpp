// Authors: Aravind Machiry, and Nilo Redini.
// University of California, Santa Barbara.

// This code is build on top of Navas's Wrapped Intervals

//////////////////////////////////////////////////////////////////////////////
/// \file  StridedWrappedRange.cpp
///        Strided Wrapped Interval Abstract Domain.
///
///////////////////////////////////////////////////////////////////////////////

#include "BaseRange.h"
#include "StridedWrappedRange.h"
#include "WrappedRange.h"
#include <iostream>
#include <algorithm>

using namespace llvm;
using namespace unimelb;

void test_GeneralizedJoin();

#define EVAL
#define SMART_JOIN

STATISTIC(NumOfOverflows     ,"Number of overflows");
STATISTIC(NumOfJoins         ,"Number of joins");
STATISTIC(NumOfJoinTies      ,"Number of join ties");

void printComparisonOpSI(unsigned Pred,raw_ostream &Out){
  switch(Pred){
  case ICmpInst::ICMP_EQ:  Out<< " = "; break;
  case ICmpInst::ICMP_NE:  Out<< " != ";  break;
  case ICmpInst::ICMP_ULE: Out << " <=_u " ;  break;
  case ICmpInst::ICMP_ULT: Out << " <_u " ;  break;
  case ICmpInst::ICMP_UGT: Out << " >_u " ;  break;
  case ICmpInst::ICMP_UGE: Out << " >=_u " ;  break;
  case ICmpInst::ICMP_SLE: Out << " <=_s " ;  break;
  case ICmpInst::ICMP_SLT: Out << " <_s " ;  break;
  case ICmpInst::ICMP_SGT: Out << " >_s " ;  break;
  case ICmpInst::ICMP_SGE: Out << " >=_s " ;  break;
  default: ;
  }
}

bool StridedWrappedRange::isBot() const { 
  return __isBottom;
}

bool StridedWrappedRange::IsTop() const {  
  return BaseRange::IsTop();
}

void StridedWrappedRange::makeBot(){ 
  __isBottom=true;
  __isTop=false;
}

void StridedWrappedRange::makeTop(){ 
  BaseRange::makeTop();
  // set this to 1, just in case.
  this->stride_val = 1;
  __isBottom=false;
}

bool StridedWrappedRange::isIdentical(AbstractValue* V){
  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);
  // check if both ranges and strided are equal
  return (BaseRange::isIdentical(V) && S->stride_val == T->stride_val);
}

bool StridedWrappedRange::isEqual(AbstractValue* V){
  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);
  // This is correct since we have a poset and the anti-symmetric
  // property holds.
  return (S->lessOrEqual(T) && T->lessOrEqual(S) && S->getStride() == T->getStride());
}

/////
// Optimized version that speed up the analysis significantly.
// This version takes advantage of the fact that JumpSet is sorted.
/////
void widenOneIntervalSI(const APInt &a, const APInt &b, unsigned int width,
                        const std::vector<int64_t> &JumpSet,
                        APInt &lb, APInt &ub) {

  // lb_It points to the first element that is not less than lb
  std::vector<int64_t>::const_iterator lb_It =
          std::lower_bound(JumpSet.begin(), JumpSet.end(), a.getSExtValue(),
                           Utilities::Lex_LessThan_Comp);

  if (lb_It == JumpSet.end()) // no element is less than a
    lb = a;
  else {
    if (lb_It == JumpSet.begin()) {
      APInt LB_LandMark(width, *(lb_It), false);
      lb = LB_LandMark;
    } else {
      APInt LB_LandMark(width, *(lb_It - 1), false);
      lb = LB_LandMark;
    }
  }

  // ub_It points to the first element that is greater than ub
  std::vector<int64_t>::const_iterator ub_It =
          std::upper_bound(JumpSet.begin(), JumpSet.end(), b.getSExtValue(),
                           Utilities::Lex_LessThan_Comp);

  if (ub_It == JumpSet.end()) // no element is greater than b
    ub = b;
  else {
    APInt UB_LandMark(width, *ub_It, false);
    ub = UB_LandMark;
  }
}

bool checkOverflowForWideningJumpSI(const APInt &Card){
  // If a or b do not fit into uint64_t or they do not have same width
  // then APInt raises an exception
  uint64_t value = Card.getZExtValue();
  // Max is 2^{w-1}
  uint64_t Max = (APInt::getSignedMaxValue(Card.getBitWidth() -1)).getZExtValue();
    
  return (value >= Max);
}

/// After trivial cases, we check in what direction we are growing and
/// doubling the size of one the intervals. We also use the constants
/// of the program to make guesses.
void StridedWrappedRange::widening(AbstractValue *PreviousV, 
                            const std::vector<int64_t> &JumpSet){
                            

  if (PreviousV->isBot()) return;
  // rest of trivial cases are handled by the caller (e.g., if any of
  // the two abstract values is top).

  StridedWrappedRange *Old = cast<StridedWrappedRange>(PreviousV->clone());  
  StridedWrappedRange *New = this;

  APInt u = Old->getLB();
  APInt v = Old->getUB();
  APInt x = New->getLB();
  APInt y = New->getUB();

  bool canDoublingInterval=true;
  APInt cardOld  = WCard(u,v);

  // Overflow check   
  if (checkOverflowForWideningJumpSI(cardOld)){
    CounterWideningCannotDoubling++;
    if (CounterWideningCannotDoubling < 5){ // here some constant value
      canDoublingInterval=false;
    }
    else{
      New->makeTop();
#ifdef EVAL
      DEBUG(dbgs() <<  *New << "\n");
#endif
      CounterWideningCannotDoubling=0;
      return;
    }
  }

  StridedWrappedRange Merged(*Old);
  Merged.join(New);  

  unsigned int width = x.getBitWidth();
  if ( Old->lessOrEqual(New) &&  
      (!Old->WrappedMember(x) && !Old->WrappedMember(y))) {
    if (!canDoublingInterval){
      APInt widen_lb; APInt widen_ub;
      widenOneIntervalSI(Merged.getLB(), Merged.getUB(), width, 
		       JumpSet, widen_lb, widen_ub);
      StridedWrappedRange tmp(x,y,width); 
      tmp.setStride(New->getStride());
      
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      New->setStride(Merged.getStride());
      New->join(&tmp);
    }
    else {
      APInt widen_lb = x;
      APInt widen_ub = x + cardOld + cardOld; 
      APInt jump_lb; APInt jump_ub;
      widenOneIntervalSI(Merged.getLB(), Merged.getUB(), width, JumpSet, jump_lb, jump_ub);
      {
        StridedWrappedRange tmp = simkSmallerInterval(Merged.getLB(), widen_lb, width);
        if (Merged.getLB() == widen_lb) {
          tmp.setStride(0);
        } else {
          tmp.setStride(1);
        }
        if (tmp.WrappedMember(jump_lb))
          widen_lb = jump_lb;
      }
      {
        StridedWrappedRange tmp = simkSmallerInterval(Merged.getUB(), widen_ub, width);
        if (Merged.getUB() == widen_ub) {
          tmp.setStride(0);
        } else {
          tmp.setStride(1);
        }
        if (tmp.WrappedMember(jump_ub))
          widen_ub = jump_ub;
      }
    StridedWrappedRange tmp(x,y,width);
    tmp.setStride(New->getStride());
      
    New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
    New->setStride(Merged.getStride());
    New->join(&tmp);
    }
  }
  else if ( (Merged.getLB() == u) && (Merged.getUB() == y)){
    if (!canDoublingInterval){
      APInt widen_lb = u; APInt widen_lb__;
      APInt widen_ub;
      widenOneIntervalSI(Merged.getLB(), Merged.getUB(), width, JumpSet, widen_lb__, widen_ub);
	    StridedWrappedRange tmp(x,y,width);
      tmp.setStride(New->getStride());
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      New->setStride(Merged.getStride());
      New->join(&tmp);
    }
    else {
      APInt widen_lb = u;
      APInt widen_ub = u + cardOld + cardOld; 
      APInt jump_lb__; APInt jump_ub;
      widenOneIntervalSI(Merged.getLB(), Merged.getUB(), width, JumpSet, jump_lb__, jump_ub);
      {
        StridedWrappedRange tmp = simkSmallerInterval(Merged.getUB(), widen_ub, width);

        if (Merged.getUB() == widen_ub) {
          tmp.setStride(0);
        } else {
          tmp.setStride(1);
        }

        if (tmp.WrappedMember(jump_ub))
          widen_ub = jump_ub;
      }
      StridedWrappedRange tmp(u,y,width);
      unsigned long new_stride = UtilFunctions::getGCD(New->getStride(), Old->getStride());
      tmp.setStride(new_stride);
      
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      New->setStride(Merged.getStride());
      New->join(&tmp);
    }
  }
  else if ( (Merged.getLB() == x) && (Merged.getUB() == v)){

    if (!canDoublingInterval){
      APInt widen_lb; 
      APInt widen_ub = v; APInt widen_ub__;
      widenOneIntervalSI(Merged.getLB(), Merged.getUB(), width, 
		       JumpSet, widen_lb, widen_ub__);
      
      StridedWrappedRange tmp(x,y,width); 
      tmp.setStride(New->getStride());
      
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      New->setStride(Merged.getStride());
      New->normalizeTop();
      New->join(&tmp);
    }
    else{
      APInt widen_lb = u - cardOld - cardOld; 
      APInt widen_ub = v;
      APInt jump_lb; APInt jump_ub__;
      widenOneIntervalSI(Merged.getLB(), Merged.getUB(), width, JumpSet, jump_lb, jump_ub__);
      {
        StridedWrappedRange tmp = simkSmallerInterval(Merged.getLB(), widen_lb, width);

        if (Merged.getLB() == widen_lb) {
          tmp.setStride(0);
        } else {
          tmp.setStride(1);
        }

        if (tmp.WrappedMember(jump_lb))
          widen_lb = jump_lb;
      }
      StridedWrappedRange tmp(x,v,width);
      unsigned long new_stride = UtilFunctions::getGCD(New->getStride(), Old->getStride());
      tmp.setStride(new_stride);
      
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      New->setStride(Merged.getStride());
      New->join(&tmp);
    }
  }
  else{
    // Otherwise, return old interval
    New->setLB(Old->getLB());
    New->setUB(Old->getUB());
    New->setStride(Old->getStride());
  }
  
  New->normalizeTop();

  return;
}

/// Return true if x \in S[a,b].
bool StridedWrappedRange::WrappedMember(const APInt &e) const{
  
  if (isBot()) return false;
  if (IsTop()) return true;
  
  if(isSingleVal()) {
    assert(getStride() == 0);
    if(getLB() == e) return true;
    return false;
  } else {
    assert(getStride() != 0);
      
    bool to_ret = false;

    APInt x = getLB();
    APInt y = getUB();

    unsigned long bw = (e.getBitWidth() > x.getBitWidth() ? e.getBitWidth():x.getBitWidth());

    bw = (bw < y.getBitWidth() ? y.getBitWidth() : bw);

    APInt et(bw, e.getZExtValue());
    APInt xt(bw, x.getZExtValue());
    APInt yt(bw, y.getZExtValue());

    to_ret =  SILex_LessOrEqual(et - xt, yt - xt);
    if(to_ret) {
      uint64_t diff_norm = (et - xt).getZExtValue();
      return ((diff_norm%getStride()) == 0);
    }
      return to_ret;
  }
}

/// Return true if this is less or equal than V based on the poset
/// ordering.
bool StridedWrappedRange::WrappedlessOrEqual(AbstractValue * V){ 
  
  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);  

  // Bottom
  if (S->isBot()) return true;
  // Top
  if (S->IsTop() && T->IsTop()) 
    return true;
  else{
    if (S->IsTop())
      return false;
    else{
      if (T->IsTop()) 
	      return true;
    }
  }

  ///
  // a \in T and b \in T and (c \in s and d \in s => s=t)
  ///
  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();
  
  if(S->isSingleVal()) {
    return T->WrappedMember(a);
  }
  if(T->isSingleVal()) {
    return false;
  }
  
  if(T->WrappedMember(a) && T->WrappedMember(b)) {
    if(a == c && b == d && (S->getStride() % T->getStride() == 0)) {
        return true;
    }
    if(!(S->WrappedMember(c)) || !(S->WrappedMember(d))) {
        assert(S->getStride() != 0 && T->getStride() != 0);
        APInt a_u(a.getBitWidth(), a.getZExtValue());
        APInt c_u(c.getBitWidth(), c.getZExtValue());
        return ((((a_u - c_u).getZExtValue() % S->getStride()) == 0) && (S->getStride() % T->getStride() == 0));
    }
  }
  return false;  
}

bool StridedWrappedRange::isMoreOrEqualPrecise(AbstractValue * V){ 
  
  StridedWrappedRange *S = this;
  WrappedRange *T = cast<WrappedRange>(V); 
  // Bottom
  if (S->isBot()) return true;
  // Top
  if (S->IsTop() && T->IsTop()) 
    return true;
  else{
    if (S->IsTop())
      return false;
    else{
      if (T->IsTop()) 
	return true;
    }
  }
  ///
  // a \in T and b \in T and (c \in s and d \in s => s=t)
  ///
  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();
  
  return ( T->WrappedMember(a) && 
	   T->WrappedMember(b) &&
	   ((a == c && b == d && S->getStride() >= T->getStride()) || 
	    !(S->WrappedMember(c)) || !(S->WrappedMember(d))));	      
}


bool StridedWrappedRange::lessOrEqual(AbstractValue * V){ 
  return WrappedlessOrEqual(V);
}

void StridedWrappedRange::print(raw_ostream &Out) const{
    BaseRange::print(Out);
}

void StridedWrappedRange::join(AbstractValue *V){
  StridedWrappedRange * R = cast<StridedWrappedRange>(V);
  if (R->isBot()) {
    return;
   }
  if (isBot()){
    WrappedRangeAssign(R);
    return;
  }

  WrappedJoin(R);
  normalizeTop();
}


void StridedWrappedRange::WrappedJoin(AbstractValue *V){

  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);

  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();
  
  NumOfJoins++;
  
  if(S->isBot()) {
    WrappedRangeAssign(T);
    return;
  }
  
  if(T->isBot()) {
    return;
  }

   if(S->isSingleVal() && T->isSingleVal()) {
     #ifdef SMART_JOIN
     APInt u;
     APInt l;
     
     uint64_t si1_card = WCard_mod(a, d);
     uint64_t si2_card = WCard_mod(c, b);
     if (si1_card <= si2_card) {
       l = a;
       u = d;
     } else {
       l = c;
       u = b;
     }
     #else
     APInt u = d;
     APInt l = a;
     #endif
       
     unsigned long new_stride = (unsigned long)(u - l).getZExtValue();
     setUB(u);
     setLB(l);
     setStride(new_stride);
     return;
   }
   
   StridedWrappedRange S_stride1(*S);
   S_stride1.AdjustStride();
   
   StridedWrappedRange T_stride1(*T);
   T_stride1.AdjustStride();
   
  // Containment cases (also cover bottom and top cases)
  if (S->WrappedlessOrEqual(T)) {
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    if(!S->isSingleVal()) {
        new_stride = T->getStride();
    }
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((a - c).getZExtValue()));
    setLB(c);
    setUB(d);
    setStride(new_stride);
  }
  else if (T->WrappedlessOrEqual(S)) {
    //WrappedRangeAssign(T);
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    if(!T->isSingleVal()) {
        new_stride = S->getStride();
    }
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((c - a).getZExtValue()));
    setStride(new_stride);
  }
  // Extra case for top: one cover the other
  else if (T_stride1.WrappedMember(a) && T_stride1.WrappedMember(b) &&
           S_stride1.WrappedMember(c) && S_stride1.WrappedMember(d)){
    makeTop();
  }
  // Overlapping cases
  else if (S_stride1.WrappedMember(c)){
    setLB(a);
    setUB(d);
    
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((c - a).getZExtValue()));
    setStride(new_stride);
  }
  else if (T_stride1.WrappedMember(a)){
    setLB(c);
    setUB(b);
    
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((a - c).getZExtValue()));
    setStride(new_stride);
  } else {
      #ifndef SMART_JOIN
      unsigned long new_stride;
      if(S->isSingleVal()) {
          new_stride = UtilFunctions::getGCD(T->getStride(), (unsigned long)((c - a).getZExtValue()));
      } else if(T->isSingleVal()) {
          new_stride = UtilFunctions::getGCD(S->getStride(), (unsigned long)((c - a).getZExtValue()));
      } else {
          new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
          uint64_t card_mod = WCard_mod(a, c);
          new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)(card_mod - (uint64_t)1));
      }
      StridedWrappedRange Res(*S);
      Res.setUB(T->getUB());
      Res.setStride(new_stride);
      WrappedRangeAssign(&Res);
      #endif

      #ifdef SMART_JOIN
      //smart join
      unsigned long new_stride, new_stride1, new_stride2;
      if(S->isSingleVal()) {
          new_stride = T->getStride();
      } else if(T->isSingleVal()) {
          new_stride = S->getStride();
      } else {
          new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
      }

      //unsigned long my_ass1 = (unsigned long)WCard_mod(c, a);
      uint64_t card_c_a = WCard_mod(c, a);
      uint64_t card_a_c = WCard_mod(a, c);

      new_stride1 = UtilFunctions::getGCD(new_stride, (unsigned long)(card_c_a - (uint64_t)1));
      new_stride2 = UtilFunctions::getGCD(new_stride, (unsigned long)(card_a_c - (uint64_t)1));

      StridedWrappedRange si1(*S);
      si1.setLB(c);
      si1.setStride(new_stride1);

      StridedWrappedRange si2(*S);
      si2.setUB(d);
      si2.setStride(new_stride2);
      uint64_t si1_card = WCard_mod(si1.getLB(), si1.getUB());
      uint64_t si2_card = WCard_mod(si2.getLB(), si2.getUB());
      uint64_t n_val1 = si1_card / ((uint64_t)new_stride1);
      uint64_t n_val2 = si2_card / ((uint64_t)new_stride2);
      if(n_val1 <= n_val2) {
        WrappedRangeAssign(&si1);//[c,b]
      } else {
          WrappedRangeAssign(&si2); //[a, d]
      }

       #endif // SMART JOIN
    }

  normalizeTop();
  // This is gross but we need to record that this is not bottom
  // anymore.
  if (!S->isBot() || !T->isBot())
    resetBottomFlag();
}

// Begin  machinery for generalized join
bool SortWrappedRanges_Compare(StridedWrappedRange *R1, StridedWrappedRange *R2){
  assert(R1);
  assert(R2);
  APInt a = R1->getLB();
  APInt c = R2->getLB();
  return SILex_LessOrEqual(a,c); // a.ule(c);
}

/// Sort a vector of wrapped ranges in order of lexicographical
/// increasing left bound.
void SortWrappedRanges(std::vector<StridedWrappedRange *> & Rs){
  std::sort(Rs.begin(), Rs.end() , SortWrappedRanges_Compare);
}

// Wrapper for join
StridedWrappedRange Extend(const StridedWrappedRange &R1, const  StridedWrappedRange &R2){  
  StridedWrappedRange Res(R1);
  StridedWrappedRange tmp(R2);
  Res.join(&tmp);
  return Res;
}

/// Return the biggest of the two wrapped intervals.
StridedWrappedRange Bigger(const StridedWrappedRange &R1, const StridedWrappedRange &R2){

  if (R1.isBot() && !R2.isBot())
    return StridedWrappedRange(R2);
  if (R2.isBot() && !R1.isBot())
    return StridedWrappedRange(R1);
  if (R2.isBot() && R1.isBot())
    return StridedWrappedRange(R1);

  APInt a = R1.getLB();
  APInt b = R1.getUB();
  APInt c = R2.getLB();
  APInt d = R2.getUB();
  //  if (WrappedRange::WCard(a,b).uge(WrappedRange::WCard(c,d)))
  if (SILex_LessOrEqual(StridedWrappedRange::WCard(c,d),StridedWrappedRange::WCard(a,b)))
    return StridedWrappedRange(R1);
  else 
    return StridedWrappedRange(R2);
}

/// If R1 and R2 overlap then return bottom. Otherwise, return the
/// clockwise distance from the end of the first to the start of the
/// second.
StridedWrappedRange ClockWiseGap(const StridedWrappedRange &R1, const StridedWrappedRange &R2){
  APInt a = R1.getLB();
  APInt b = R1.getUB();
  APInt c = R2.getLB();
  APInt d = R2.getUB();

  StridedWrappedRange gap(b+1,c-1,a.getBitWidth());
  if (R1.isBot() || R2.isBot() || R2.WrappedMember(b) || R1.WrappedMember(c))
    gap.makeBot();
  
  return gap;
}

/// Return the complement of a wrapped interval.
StridedWrappedRange WrappedComplement(const StridedWrappedRange &R){
  StridedWrappedRange C(R);

  if (R.isBot()){
    C.makeTop();
    return C;
  }
  if (R.IsTop()){
    C.makeBot();
    return C;
  }
  
  APInt x = C.getLB();
  APInt y = C.getUB();
  C.setLB(y+1);
  C.setUB(x-1);
  unsigned long new_dist = (unsigned long)StridedWrappedRange::WCard_mod(C.getLB(), C.getUB());
  new_dist--;
  unsigned long new_stride;
  
  if(new_dist == 0) {
    new_stride = 0;
  } else if(R.getStride() == 0) {
    new_stride = 1;
  } else {
    new_stride = UtilFunctions::getGCD(R.getStride(), new_dist);
  }
  
  C.setStride(new_stride);
  return C;
}


/// Return true if starting from 0....0 (South Pole) we encounter y
/// before than x. This coincides with unsigned less or equal.
inline bool CrossSouthPole(const APInt &x,  const APInt &y)  {
  return y.ult(x);
}

/// Return true if starting from 2^{w-1} (North Pole) we encounter y
/// before than x. This coincides with signed less or equal.
inline bool CrossNorthPole(const APInt &x,  const APInt &y)  {
  return (y.slt(x));
}


inline StridedWrappedRange * convertAbsValToWrapped(AbstractValue *V){
  return cast<StridedWrappedRange>(V);
}

inline AbstractValue * convertPtrValToAbs(StridedWrappedRangePtr V){
  return cast<AbstractValue>(V.get());
}

void StridedWrappedRange::
GeneralizedJoin(std::vector<AbstractValue *> Values){

  if (Values.size() < 2) return;

  std::vector<StridedWrappedRange*> Rs;
  std::transform(Values.begin(), Values.end(), 
		 std::back_inserter(Rs), 
		 convertAbsValToWrapped);

  SortWrappedRanges(Rs);  

  StridedWrappedRange f(*this);
  f.makeBot();

  for(std::vector<StridedWrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    StridedWrappedRange R(*(*I));
    if (R.IsTop() || CrossSouthPole(R.getLB(), R.getUB())){      
      f = Extend(f, R);
    }
  }

  StridedWrappedRange g(*this);
  g.makeBot();
  for(std::vector<StridedWrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    StridedWrappedRange R(*(*I));
    StridedWrappedRange tmp = ClockWiseGap(f, R);
    g = Bigger(g,tmp);
    f = Extend(f, R);
  }

  StridedWrappedRange Tmp = WrappedComplement(Bigger(g,WrappedComplement(f)));
  this->setLB(Tmp.getLB());
  this->setUB(Tmp.getUB());
}

StridedWrappedRange rotatingGenJoin(std::vector<StridedWrappedRange*> vals, long curr_ind) {
    unsigned long count= 0;
    StridedWrappedRange curr_val(*vals.front());
    curr_val.makeBot();
    
    while(count < vals.size()) {
        curr_val.WrappedJoin(vals[curr_ind]);
        curr_ind = (curr_ind + 1) % vals.size();
        count++;
    }
    
    return curr_val;
}


bool StridedWrappedRange::
StridedGeneralizedJoin(std::vector<AbstractValue *> Values, StridedWrappedRange *result){
  if (Values.size() < 1) return false;
  
  if(Values.size() == 1) {
    StridedWrappedRange *R1 = cast<StridedWrappedRange>(Values.front());
    *result = *R1;
    return true;
   }
   
   if(Values.size() == 2) {
    StridedWrappedRange *R1 = cast<StridedWrappedRange>(Values.front());
    StridedWrappedRange temp(*R1);
    temp.WrappedJoin(Values.back());
    *result = temp;
    return true;     
   }

  std::vector<StridedWrappedRange*> Rs;
  std::transform(Values.begin(), Values.end(), 
		 std::back_inserter(Rs), 
		 convertAbsValToWrapped);

  SortWrappedRanges(Rs);  

  StridedWrappedRange f(*(Rs.front()));
  f.makeBot();
  
  for(unsigned long i=0; i<Rs.size(); i++) {
    StridedWrappedRange R = rotatingGenJoin(Rs, i);
    if(i == 0) {
        f = R;
    }
    uint64_t r_vals, f_vals;
    if(R.isSingleVal()) {
        r_vals = 1;
    } else {
        r_vals = (WCard_mod(R.getLB(), R.getUB()) / (uint64_t)R.getStride()) + (uint64_t)1;
    }
    if(f.isSingleVal()) {
        f_vals = 1;
    } else{
        f_vals = (WCard_mod(f.getLB(), f.getUB()) / (uint64_t)f.getStride()) + (uint64_t)1;
    }
    if(r_vals < f_vals) {
        f = R;
    }
  }
  
  *result = f;
  return true;
}

// End  Machinery for generalized join

void StridedWrappedRange::meet(AbstractValue *V1, AbstractValue *V2){
			  
  StridedWrappedRange * R1 = cast<StridedWrappedRange>(V1);
  StridedWrappedRange * R2 = cast<StridedWrappedRange>(V2);

  this->makeBot();
  StridedWrappedRange tmp = StridedWrappedMeet(R1,R2);
  this->WrappedJoin(&tmp);
}

std::vector<StridedWrappedRangePtr> StridedWrappedRange::MultiValueIntersection(StridedWrappedRange *Op1, StridedWrappedRange *Op2) {

    std::vector<StridedWrappedRangePtr> res;
    if(Op1->isBot() || Op2->isBot()) {
        StridedWrappedRange toRet(*Op1);
        toRet.makeBot();
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
    }

    if(Op1->isSingleVal() && Op2->isSingleVal()) {
        if(Op1->getLB() == Op2->getLB()) {
            APInt lb = Op1->getLB();
            StridedWrappedRange toRet(*Op1);
            toRet.setLB(lb);
            toRet.setUB(lb);
            toRet.setStride(0);
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
            return res;
        }
        StridedWrappedRange toRet(*Op1);
        toRet.makeBot();
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
    }
    
   if(Op1->isSingleVal()) {
        APInt lb = Op1->getLB();
        if((((Op2->getLB() - lb).getZExtValue() % Op2->getStride()) == 0) && Op2->WrappedMember(lb)) {
            StridedWrappedRange toRet(*Op1);
            toRet.setLB(lb);
            toRet.setUB(lb);
            toRet.setStride(0);
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
            return res;
        }
        StridedWrappedRange toRet(*Op1);
        toRet.makeBot();
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
    }

    if(Op2->isSingleVal()) {
        APInt lb = Op2->getLB();
        if((((Op1->getLB() - lb).getZExtValue() % Op1->getStride()) == 0) && Op1->WrappedMember(lb)) {
            StridedWrappedRange toRet(*Op2);
            toRet.setLB(lb);
            toRet.setUB(lb);
            toRet.setStride(0);
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
            return res;
        }
        StridedWrappedRange toRet(*Op1);
        toRet.makeBot();
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
    }
    unsigned long new_stride = UtilFunctions::getLCM(Op1->getStride(), Op2->getStride());
    APInt lb1 = Op1->getLB();
    APInt ub1 = Op1->getUB();
    APInt lb2 = Op2->getLB();
    APInt ub2 = Op2->getUB();
    if(Op1->WrappedlessOrEqual(Op2)) {
        APInt result;
        if(!StridedWrappedRange::minimal_common_integer(Op1, Op2, &result)) {
            StridedWrappedRange toRet(*Op1);
            toRet.makeBot();
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
            return res;
        }
        unsigned long long_val;
        long_val = (unsigned long)((((ub1 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
        APInt newub(ub1.getBitWidth(), long_val);
        StridedWrappedRange toRet(*Op1);
        toRet.setLB(result);
        toRet.setUB(newub);
        toRet.setStride(new_stride);
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
                
    }
    else if(Op2->WrappedlessOrEqual(Op1)) {
        APInt result;
        if(!StridedWrappedRange::minimal_common_integer(Op1, Op2, &result)) {
            StridedWrappedRange toRet(*Op1);
            toRet.makeBot();
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
            return res;
        }        
        unsigned long long_val;
        long_val = (unsigned long)((((ub2 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
        APInt newub(ub2.getBitWidth(), long_val);
        StridedWrappedRange toRet(*Op1);
        toRet.setLB(result);
        toRet.setUB(newub);
        toRet.setStride(new_stride);
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
    } 
    else if(Op1->WrappedMember(lb2) && Op1->WrappedMember(ub2) && Op2->WrappedMember(lb1) && Op2->WrappedMember(ub1)) {
        APInt result;
        StridedWrappedRange s0(*Op1);
        s0.setUB(ub2);
        StridedWrappedRange s1(*Op1);
        s1.setUB(ub1);
        
        if(!StridedWrappedRange::minimal_common_integer(&s0, Op2, &result)) {
            StridedWrappedRange toRet(*Op1);
            toRet.makeBot();
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
        } else {
            unsigned long long_val;
            long_val = (unsigned long)((((ub2 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
            APInt newub(ub2.getBitWidth(),long_val);
            StridedWrappedRange toRet(*Op1);
            toRet.setLB(result);
            toRet.setUB(newub);
            toRet.setStride(new_stride);
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
        }
        
        if(!StridedWrappedRange::minimal_common_integer(&s1, Op1, &result)) {
            StridedWrappedRange toRet(*Op1);
            toRet.makeBot();
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
        } else {            
            unsigned long long_val;
            long_val = (unsigned long)((((ub1 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
            APInt newub(ub1.getBitWidth(), long_val);
            StridedWrappedRange toRet(*Op1);
            toRet.setLB(result);
            toRet.setUB(newub);
            toRet.setStride(new_stride);
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
        }
        return res;
    }
    else if(Op1->WrappedMember(lb2)) {
        APInt result;
        if(!StridedWrappedRange::minimal_common_integer(Op2, Op1, &result)) {
            StridedWrappedRange toRet(*Op1);
            toRet.makeBot();
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
            return res;
        }
        unsigned long long_val;
        long_val = (unsigned long)((((ub1 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
        APInt newub(ub1.getBitWidth(), long_val);
        StridedWrappedRange toRet(*Op1);
        toRet.setLB(result);
        toRet.setUB(newub);
        toRet.setStride(new_stride);
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
        
    }
    else if(Op2->WrappedMember(lb1)) {
        APInt result;
        if(!StridedWrappedRange::minimal_common_integer(Op1, Op2, &result)) {
            StridedWrappedRange toRet(*Op1);
            toRet.makeBot();
            StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
            res.push_back(s1);
            return res;
        }
        unsigned long long_val;
        long_val = (unsigned long)((((ub2 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
        APInt newub(ub2.getBitWidth(), long_val);
        StridedWrappedRange toRet(*Op1);
        toRet.setLB(result);
        toRet.setUB(newub);
        toRet.setStride(new_stride);
        StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
        res.push_back(s1);
        return res;
    }
    //Disjoint case
    StridedWrappedRange toRet(*Op1);
    toRet.makeBot();
    StridedWrappedRangePtr s1(new StridedWrappedRange(toRet));
    res.push_back(s1);
    return res;
    
}

StridedWrappedRange unimelb::
StridedWrappedMeet(StridedWrappedRange *S, StridedWrappedRange *T){
  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();

  APInt lb; APInt ub;
  unsigned int width = a.getBitWidth();
  unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());

  // Containment cases (also cover bottom and top cases)
  if (S->WrappedlessOrEqual(T)) {
    lb = S->getLB();
    ub = S->getUB();
  }
  else if (T->WrappedlessOrEqual(S)) {
    lb = T->getLB();
    ub = T->getUB();
  }
  // If one cover the other the meet is not convex.  We return the one
  //  with smallest cardinality
  else if (T->WrappedMember(a) && T->WrappedMember(b) &&
	   S->WrappedMember(c) && S->WrappedMember(d)){
    if ( SILex_LessThan(StridedWrappedRange::WCard(a,b), StridedWrappedRange::WCard(c,d)) || ( StridedWrappedRange::WCard(a,b) == StridedWrappedRange::WCard(c,d) && SILex_LessOrEqual(a,c))){
      lb = S->getLB();
      ub = S->getUB();
    }
    else{
      lb = T->getLB();
      ub = T->getUB();
    }
  }
  // Overlapping cases
  else if (S->WrappedMember(c)){
    lb = c;
    ub = b;
  }
  else if (T->WrappedMember(a)){
    lb = a;
    ub = d;
  }
  else{
    // Otherwise, bottom
    // a and b to put something initilized.
    StridedWrappedRange Meet(a,b,width);   
    Meet.makeBot();
    return Meet;
  }
  
  StridedWrappedRange Meet(lb,ub,width, new_stride);   
  Meet.normalizeTop();
  return Meet;
  
}

// Comparison operations: these methods are used to tell if the
// evaluation of a guard is true or false.  If return false then it's
// the evaluation of the guard is definite false. If true then we must
// still check the negation of the condition. If also true then the
// evaluation of the guard will be finally "maybe". Otherwise,
// definitely true. 
// Very importantly, these operations depend on the sign. 

/// [a,b] <= [c,d] if a <= d.
inline bool comparisonSle_SameHemisphere(StridedWrappedRange *I1, StridedWrappedRange *I2){
  return I1->getLB().sle(I2->getUB());
}

/// [a,b] < [c,d] if a < d.
inline bool comparisonSlt_SameHemisphere(StridedWrappedRange *I1, StridedWrappedRange *I2){
  return I1->getLB().slt(I2->getUB());
}

/// [a,b] <= [c,d] if a <= d.
inline bool comparisonUle_SameHemisphere(StridedWrappedRange *I1, StridedWrappedRange *I2){
  return I1->getLB().ule(I2->getUB());
}

/// [a,b] < [c,d]  if a < d.
inline bool comparisonUlt_SameHemisphere(StridedWrappedRange *I1, StridedWrappedRange *I2){
  return I1->getLB().ult(I2->getUB());
}

bool comparisonSignedLessThan(StridedWrappedRange *I1,StridedWrappedRange *I2, bool IsStrict){
  // If IsStrict=true then <= else <
  // **NORTH POLE SPLIT** and do normal test for all possible
  // pairs. If one is true then return true.
  std::vector<StridedWrappedRangePtr> s1 = 
    StridedWrappedRange::strided_nsplit(I1->getLB(), I1->getUB(), 
			 I1->getLB().getBitWidth(), I1->getStride());
  std::vector<StridedWrappedRangePtr> s2 = 
    StridedWrappedRange::strided_nsplit(I2->getLB(), I2->getUB(), 
			 I2->getLB().getBitWidth(), I2->getStride());
  bool tmp=false;
  typedef std::vector<StridedWrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      if (IsStrict)
	      tmp |= comparisonSlt_SameHemisphere((*I1).get(), (*I2).get());
      else
	      tmp |= comparisonSle_SameHemisphere((*I1).get(), (*I2).get());
      if (tmp) {
	      // we dont' bother check all of them if one is already true
	      return true;
      }
    }    
  }
  return tmp;
}

 bool comparisonUnsignedLessThan(StridedWrappedRange *I1, StridedWrappedRange *I2, 
				 bool IsStrict){
  // If IsStrict=true then <= else <
  // **SOUTH POLE SPLIT** and do normal test for all possible
  // pairs. If one is true then return true.
  std::vector<StridedWrappedRangePtr> s1 = 
    StridedWrappedRange::strided_ssplit(I1->getLB(), I1->getUB(), 
			 I1->getLB().getBitWidth(), I1->getStride());
  std::vector<StridedWrappedRangePtr> s2 = 
    StridedWrappedRange::strided_ssplit(I2->getLB(), I2->getUB(), 
			 I2->getLB().getBitWidth(), I2->getStride());

  bool tmp=false;
  typedef std::vector<StridedWrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      if (IsStrict)
	      tmp |= comparisonUlt_SameHemisphere((*I1).get(), (*I2).get());
      else
	      tmp |= comparisonUle_SameHemisphere((*I1).get(), (*I2).get());
      if (tmp){
	      // we dont' bother check all of them if one is already true
	      return true;
      }
    }    
  }
  return tmp;
}

bool StridedWrappedRange::comparisonSle(AbstractValue *V){
  StridedWrappedRange *I1 = this;
  StridedWrappedRange *I2 = cast<StridedWrappedRange>(V);  
  return comparisonSignedLessThan(I1,I2,false);
}

bool StridedWrappedRange::comparisonSlt(AbstractValue *V){
  StridedWrappedRange *I1 = this;
  StridedWrappedRange *I2 = cast<StridedWrappedRange>(V);  
  I1->normalizeTop();
  I2->normalizeTop();
  return comparisonSignedLessThan(I1,I2,true);
}

bool StridedWrappedRange::comparisonUle(AbstractValue *V){
  StridedWrappedRange *I1 = this;
  StridedWrappedRange *I2 = cast<StridedWrappedRange>(V);  
  return comparisonUnsignedLessThan(I1,I2,false);
}

bool StridedWrappedRange::comparisonUlt(AbstractValue *V){
  StridedWrappedRange *I1 = this;
  StridedWrappedRange *I2 = cast<StridedWrappedRange>(V);  
  return comparisonUnsignedLessThan(I1,I2,true);

}

// Filter methods: they can refine an interval by using information
// from other variables that appear in the guards.

std::vector<std::pair<StridedWrappedRangePtr,StridedWrappedRangePtr> > 
keepOnlyFeasibleRanges(unsigned Pred, 
		       StridedWrappedRange *V1, StridedWrappedRange *V2){
		       
  V1->normalizeTop();
  V2->normalizeTop();

  std::vector<std::pair<StridedWrappedRangePtr,StridedWrappedRangePtr> > res;
  std::vector<StridedWrappedRangePtr> s1,s2;

  if (BaseRange::IsSignedCompInst(Pred)){
    // **NORTH POLE SPLIT**
    s1 = StridedWrappedRange::strided_nsplit(V1->getLB(), V1->getUB(),
			      V1->getLB().getBitWidth(), V1->getStride());
    s2 = StridedWrappedRange::strided_nsplit(V2->getLB(), V2->getUB(), 
			      V2->getLB().getBitWidth(), V2->getStride());
  }
  else{
    // **SOUTH POLE SPLIT**
    s1 = StridedWrappedRange::strided_ssplit(V1->getLB(), V1->getUB(), 
			      V1->getLB().getBitWidth(), V1->getStride());
    s2 = StridedWrappedRange::strided_ssplit(V2->getLB(), V2->getUB(), 
			      V2->getLB().getBitWidth(), V2->getStride());
  }
      
  typedef std::vector<StridedWrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      switch(Pred){
        case ICmpInst::ICMP_EQ:
        case ICmpInst::ICMP_NE:
          res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_SLE:
          if (comparisonSignedLessThan((*I1).get(), (*I2).get(), false))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_SLT:
          if (comparisonSignedLessThan((*I1).get(), (*I2).get(), true))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_ULE:
          if (comparisonUnsignedLessThan((*I1).get(), (*I2).get(), false))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_ULT:
          if (comparisonUnsignedLessThan((*I1).get(), (*I2).get(), true))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_SGT:
          if (comparisonSignedLessThan((*I2).get(), (*I1).get(), true))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_SGE:
          if (comparisonSignedLessThan((*I2).get(), (*I1).get(), false))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_UGT:
          if (comparisonUnsignedLessThan((*I2).get(), (*I1).get(), true))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
        case ICmpInst::ICMP_UGE:
          if (comparisonUnsignedLessThan((*I2).get(), (*I1).get(), false))
            res.push_back(std::make_pair((*I1), (*I2)));
          break;
      } // end switch
    } // end inner for
  } //end outer for 

  return res;
}

/// V1 is the range we would like to improve using information from
/// Pred and V2. Therefore, in case we cannot improve we must return
/// V1.
void StridedWrappedRange::
filterSigma(unsigned Pred, AbstractValue *V1, AbstractValue *V2){

  StridedWrappedRange *Var1   = cast<StridedWrappedRange>(V1);
  StridedWrappedRange *Var2   = cast<StridedWrappedRange>(V2);
  StridedWrappedRange Tmp(*this);

  typedef std::pair<StridedWrappedRangePtr,StridedWrappedRangePtr> WrappedPtrPair;
  std::vector<WrappedPtrPair> s = keepOnlyFeasibleRanges(Pred,Var1,Var2);
  // During narrowing (this) has a value from the fixpoint computation
  // which we want to (hopefully) improve. This is why we make this bottom. 
  this->makeBot();

  for (std::vector<WrappedPtrPair>::iterator 
	 I = s.begin(), E = s.end(); I!=E; ++I){
    StridedWrappedRange * WI1 = I->first.get();
    StridedWrappedRange * WI2 = I->second.get();
    // Note that we have only two cases since I1 is the default
    // value for the sigma node unless it can be improved using I2.
    //
    // We have two specialized methods if I2 is also a constant
    // interval or not.
    if (WI2->IsConstantRange()){
      Tmp.filterSigma_VarAndConst(Pred, WI1, WI2);
      this->WrappedJoin(&Tmp);
    }
    else{
      Tmp.filterSigma_TwoVars(Pred, WI1, WI2);
      Tmp.normalizeTop();
      this->WrappedJoin(&Tmp);
    }
  } //end for  

  // IMPORTANT: if after cutting intervals at poles, refine them (if
  // possible) and join finally them the result is bottom then it
  // means that could not improve so we should assign Var1 to this
  if (this->isBot())
    this->WrappedRangeAssign(Var1);
  this->normalizeTop();
  return;
}


/// Special case when one is variable and the other a constant in the
/// branch condition.
/// Pre: V is not top because it has been split before at the poles
void StridedWrappedRange::
filterSigma_VarAndConst(unsigned Pred, StridedWrappedRange *V, StridedWrappedRange *N){
  // Assumption: V is the range we would like to improve using   
  // information from Pred and N
  StridedWrappedRange *LHS = this;
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the meet operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  // V can be a constant interval after we split at the poles!
  switch (Pred){
  case ICmpInst::ICMP_EQ:
    { /* if v == n then [n,n] */       
      LHS->setLB(N->getLB());
      LHS->setUB(N->getUB());
      LHS->setStride(N->getStride());    
      return;
    }
  case ICmpInst::ICMP_NE:
    {
      // this can happen after we split at the poles
      if (V->isGammaSingleton() && V->isEqual(N)){
	      LHS->makeBot();
      }
      else{
	// The only case to improve the range of V is in case N is
	// either the upper bound of V or its lower bound. This case
	// doesn't change wrt to the unwrapped case.
	if (V->getLB() == N->getLB())
	  LHS->setLB(V->getLB() + 1);      
	else
	  LHS->setLB(V->getLB());

	if (V->getUB() == N->getUB())
	  LHS->setUB(V->getUB() - 1);
	else
	  LHS->setUB(V->getUB());
	  if(LHS->getLB() == LHS->getUB()) {
	    LHS->setStride(0);
	  } else {
	    LHS->setStride(V->getStride());             
	  }
    }
      return;
    }
  case ICmpInst::ICMP_ULE:
  case ICmpInst::ICMP_SLE:
    { /* if v <= n then rng(v) /\ [-oo,n] */      
      // prepare the range [-oo,n]
      // we use signed or unsigned min depending on the instruction
      StridedWrappedRange TmpRng(*N);      
      TmpRng.setLB(getMinValue(Pred)); 	      
      if(TmpRng.getLB() != TmpRng.getUB()) {
        TmpRng.setStride(1);
      }
      StridedWrappedRange meet = StridedWrappedMeet(V,&TmpRng);
      if (meet.isBot()){
        // we return bottom because this method is called on each
        // segment after cutting the original interval. If the meet of
        // two segments is bottom it doesn't mean that we have to give
        // up and assign V to LHS.
        LHS->makeBot(); //LHS->WrappedRangeAssign(V);
      }
      else
      	LHS->WrappedRangeAssign(&meet);
      return;
    }
  case ICmpInst::ICMP_ULT:	  
  case ICmpInst::ICMP_SLT:	  
    { /* if v < n then rng(v) /\ [-oo,n-1] */
      // prepate the range [-oo,n-1]
      // we use signed or unsigned min depending on the instruction
      StridedWrappedRange TmpRng(*N);      
      TmpRng.setLB(getMinValue(Pred));      
      // if (N->getLB() == APInt::getMinValue(LHS->getWidth())) // to avoid overflow
      // 	TmpRng->setUB(N->getLB());        
      // else
      TmpRng.setUB(N->getLB() - 1);
      if(TmpRng.getLB() != TmpRng.getUB()) {
        TmpRng.setStride(1);
      }   	
      StridedWrappedRange meet = StridedWrappedMeet(V,&TmpRng);

      if (meet.isBot())
	LHS->makeBot(); //LHS->WrappedRangeAssign(V);
      else
	LHS->WrappedRangeAssign(&meet);
      return;
    }
  case ICmpInst::ICMP_UGT:
  case ICmpInst::ICMP_SGT:
    { /* if v > n then  rng(v) /\ [n+1,+oo] */ 
      // prepare range [n+1,+oo]
      // we use signed or unsigned max depending on the instruction
      StridedWrappedRange TmpRng(*N);
      TmpRng.setUB(getMaxValue(Pred));
      // if (N->getUB() == APInt::getMaxValue(LHS->getWidth())) // to avoid overflow
      // 	TmpRng->setLB(N->getUB());       
      // else
      TmpRng.setLB(N->getUB() + 1);       
      
      if(TmpRng.getLB() != TmpRng.getUB()) {
        TmpRng.setStride(1);
      }
      
      StridedWrappedRange meet = StridedWrappedMeet(V,&TmpRng);
      if (meet.isBot())
	LHS->makeBot(); // LHS->WrappedRangeAssign(V);
      else
	LHS->WrappedRangeAssign(&meet);
      return;
    }    
  case ICmpInst::ICMP_UGE:
  case ICmpInst::ICMP_SGE:
    { /* if v >= n then  rng(v) /\ [n,+oo] */ 
      // prepare the range [n,+oo]
      // we use signed or unsigned max depending on the instruction
      StridedWrappedRange TmpRng(*N);
      TmpRng.setLB(N->getUB()); 
      TmpRng.setUB(getMaxValue(Pred)); 
      
      if(TmpRng.getLB() != TmpRng.getUB()) {
        TmpRng.setStride(1);
      }
      
      StridedWrappedRange meet = StridedWrappedMeet(V,&TmpRng);
      if (meet.isBot())
	LHS->makeBot(); // LHS->WrappedRangeAssign(V);
      else
	LHS->WrappedRangeAssign(&meet);
      return;
    }  
  default:
    llvm_unreachable("Unexpected error in filterSigma_VarAndConst");
  }
}

/// The condition of the branch involves two variables.
/// I1 is the range we would like to improve using information from
/// Pred and I2.
///
/// Pre: I1 and I2 are not top because they have been split before at
/// the poles.
void StridedWrappedRange::
  filterSigma_TwoVars(unsigned Pred, StridedWrappedRange *I1, StridedWrappedRange *I2){
		      
  StridedWrappedRange *LHS  = this;  
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the meet operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  // V can be a constant interval after we split at the poles!
  // assert(!I1->IsConstantRange() &&  !I2->IsConstantRange());

  // Special cases first
  if (I2->isBot()){ 
    // FIXME: If I2 is bottom, we dont' have chance to improve I1
    // It should be probably bottom but to return the I1's bounds is
    // sound. For comparison reasons, ensure always that Range and
    // WrappedRange do the same.
    LHS->setLB(I1->getLB());
    LHS->setUB(I1->getUB());    
    LHS->setStride(I1->getStride());
    return;
  }

  ///// KEY OPERATION and difference wrt to Range class.  FIXME: we
  ///// should have this operation like a template for reusing
  StridedWrappedRange meet =  StridedWrappedMeet(I1,I2);

  if (meet.isBot()){
    // If I1 and I2 are disjoint we don't have chance to improve I1
    // E.g. [0,2] < [10,50]
    // The meet here is bottom so we cannot improve
    // LHS->setLB(I1->getLB());
    // LHS->setUB(I1->getUB());    
    //
    // (*)Improvement: we can return bottom because this method is called
    // on each segment after cutting the original interval. If the
    // meet of two segments is bottom it doesn't mean that we have to
    // give up and assign V to LHS. The caller will take care of this.
    LHS->makeBot();
    return;
  }
  else{
    LHS->setLB(meet.getLB());
    LHS->setUB(meet.getUB());   
    LHS->setStride(meet.getStride()); 
  }

  switch(Pred){
  case ICmpInst::ICMP_EQ: 
    // LHS is the meet between I1 and I2
    return;
  case ICmpInst::ICMP_NE:  
      // this can happen after we split at the poles
     if (I1->isGammaSingleton() && I1->isEqual(I2)){
       LHS->makeBot();
     }
      else{
        LHS->setLB(I1->getLB());
        LHS->setUB(I1->getUB());
        LHS->setStride(I1->getStride());
        // Minor improvement if I2 is a point
        if (I2->getLB() == I2->getUB()){
          if (I1->getLB() == I2->getLB())
            LHS->setLB(LHS->getLB()+1);
          if (I1->getUB() == I2->getUB())
            LHS->setUB(LHS->getUB()-1);
        }
      }
      return;
  case ICmpInst::ICMP_ULT: // I1 <  I2
  case ICmpInst::ICMP_ULE: // I1 <= I2
  case ICmpInst::ICMP_SLT: // I1 <  I2
  case ICmpInst::ICMP_SLE: // I1 <= I2
    {
      APInt a = I1->getLB();
      APInt b = I1->getUB();
      APInt c = I2->getLB();
      APInt d = I2->getUB();

      bool IsSignedOp = (Pred==ICmpInst::ICMP_SGE || Pred==ICmpInst::ICMP_SGT);

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
	
	    LHS->setStride(UtilFunctions::getGCD(I1->getStride(), I2->getStride()));
    }
    return;
  case ICmpInst::ICMP_UGT: 
  case ICmpInst::ICMP_UGE: 
  case ICmpInst::ICMP_SGT: 
  case ICmpInst::ICMP_SGE: 
    {
      bool IsSignedOp = (Pred == ICmpInst::ICMP_SGE || Pred == ICmpInst::ICMP_SGT);
      APInt a = I1->getLB();
      APInt b = I1->getUB();
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
	    LHS->setStride(UtilFunctions::getGCD(I1->getStride(), I2->getStride()));
    }
    return;
  default: ;
  }
}

////
// Begin overflow checks  for arithmetic operations
////

/// Return true iff overflow during addition or substraction (same
/// condition).
bool IsWrappedOverflow_AddSubSI(const APInt &a, const APInt &b, const APInt &c, const APInt &d){
  // a,b,c,d are unsigned 
  //
  // If the four APInt's do not have the same width then APInt raises
  // an exception.
  unsigned width = a.getBitWidth();
  APInt tmp1  = StridedWrappedRange::WCard(a,b);  
  APInt tmp2  = StridedWrappedRange::WCard(c,d);  
  // If tmp1 or tmp2 do not fit into uint64_t then APInt raises an
  // exception.
  uint64_t n1  =  tmp1.getZExtValue();
  uint64_t n2  =  tmp2.getZExtValue();
  uint64_t Max = (APInt::getMaxValue(width)).getZExtValue() + 1;
  return ((n1 + n2) > Max);
}


/// Return true iff overflow during left shift.
bool IsWrappedOverflow_Shl(StridedWrappedRange * Op, const APInt &shift){
  APInt a = Op->getLB();
  APInt b = Op->getUB();
  APInt tmp  = StridedWrappedRange::WCard(a,b);
  // If tmp does not fit into uint64_t then APInt raises an exception.
  uint64_t n   =  tmp.getZExtValue() << shift.getZExtValue();
  uint64_t Max = (APInt::getMaxValue(a.getBitWidth())).getZExtValue() + 1; 
  return (n > Max);
}

////
// End overflow checks  for arithmetic operations
////

////
// Begin machinery for arithmetic and bitwise operations
////

/// Cut only at north pole
std::vector<StridedWrappedRangePtr> 
StridedWrappedRange::nsplit(const APInt &x, const APInt &y, unsigned width){

  // Temporary wrapped interval for north pole
  APInt NP_lb = APInt::getSignedMaxValue(width); // 0111...1
  APInt NP_ub = APInt::getSignedMinValue(width); // 1000...0
  StridedWrappedRange NP(NP_lb,NP_ub,width);

  // Temporary wrapped interval 
  StridedWrappedRangePtr s(new StridedWrappedRange(x,y,width));

  std::vector<StridedWrappedRangePtr> res;
  if (!(NP.WrappedlessOrEqual(s.get()))){
    ////
    // No need of split
    ////
    res.push_back(s);
    return res;
  }
  else{
    // Split into two wrapped intervals
    StridedWrappedRangePtr s1(new StridedWrappedRange(x,NP_lb,width)); // [x,  0111...1]
    StridedWrappedRangePtr s2(new StridedWrappedRange(NP_ub,y,width)); // [1000....0, y]
    res.push_back(s1);
    res.push_back(s2);
    return res;  
  }
}


std::vector<StridedWrappedRangePtr> 
StridedWrappedRange::strided_nsplit(const APInt &x, const APInt &y, unsigned width, unsigned long orig_stride){

  // Temporary wrapped interval for north pole
  APInt NP_lb = APInt::getSignedMaxValue(width); // 0111...1
  APInt NP_ub = APInt::getSignedMinValue(width); // 1000...0
  StridedWrappedRange NP(NP_lb,NP_ub,width);

  // Temporary wrapped interval 
  StridedWrappedRangePtr s(new StridedWrappedRange(x,y,width,orig_stride));
  
  bool stradling = false;
  if(!SILex_LessThan(y, NP_ub)) {
    if(SILex_LessThan(y, x)) {
         stradling = true;   
    } else {
        if(SILex_LessOrEqual(x, NP_lb)) {
          stradling = true;
        }
    }
    } else {
      if(SILex_LessThan(y, x) && SILex_LessOrEqual(x, NP_lb)) {
        stradling = true;
      }
    }

  std::vector<StridedWrappedRangePtr> res;
  if (/*!(NP.WrappedlessOrEqual(s.get())) || s->isSingleVal()*/!stradling){
    ////
    // No need of split
    ////
    res.push_back(s);
        return res;
  }
  else{
    // Split into two wrapped intervals
    StridedWrappedRange *s1_obj = new StridedWrappedRange(x,NP_lb,width, orig_stride);
    APInt new_ub = NP_lb - ((NP_lb - x).getZExtValue() % orig_stride);
    
    s1_obj->setUB(new_ub);
    s1_obj->setStride(orig_stride);
    s1_obj->normalizeTop();

    StridedWrappedRangePtr s1(s1_obj); // [x,  0111...1]
    s1_obj = new StridedWrappedRange(NP_ub,y,width, orig_stride);
    s1_obj->setStride(orig_stride);
    
    APInt new_lb = new_ub + orig_stride;
    s1_obj->setLB(new_lb);
    s1_obj->normalizeTop();
    StridedWrappedRangePtr s2(s1_obj); // [1000....0, y]

    res.push_back(s1);
    res.push_back(s2);
    return res;
  }
}


/// Cut only at south pole
std::vector<StridedWrappedRangePtr> 
StridedWrappedRange::ssplit(const APInt &x, const APInt &y, unsigned width){
  // Temporary wrapped interval for south pole
  APInt SP_lb = APInt::getMaxValue(width); // 111...1
  APInt SP_ub(width, 0, false);
  //                    ^^^^^ unsigned
  StridedWrappedRange SP(SP_lb,SP_ub,width);
  // Temporary wrapped interval 
  StridedWrappedRangePtr s(new StridedWrappedRange(x,y,width));

  std::vector<StridedWrappedRangePtr> res;
  if (/*!(SP.WrappedlessOrEqual(s.get()))*/ SILex_LessOrEqual(x, y)){
    ////
    // No need of split
    ////
    res.push_back(s);
    return res;
  }
  else{
    // Split into two wrapped intervals
    StridedWrappedRangePtr s1(new StridedWrappedRange(x,SP_lb,width)); // [x, 111....1]
    StridedWrappedRangePtr s2(new StridedWrappedRange(SP_ub,y,width)); // [000...0,  y] 
    res.push_back(s1);
    res.push_back(s2);
    return res;  
  }
}

/// Cut only at south pole
std::vector<StridedWrappedRangePtr>
StridedWrappedRange::strided_ssplit(const APInt &x, const APInt &y, unsigned width, unsigned long orig_stride){
  // Temporary wrapped interval for south pole
  APInt SP_lb = APInt::getMaxValue(width); // 111...1
  APInt SP_ub(width, 0, false);
  //                    ^^^^^ unsigned
  StridedWrappedRange SP(SP_lb,SP_ub,width,1);
  // Temporary wrapped interval 
  StridedWrappedRangePtr s(new StridedWrappedRange(x,y,width, orig_stride));
  
  std::vector<StridedWrappedRangePtr> res;
  if (y.getZExtValue() >= x.getZExtValue()){
    ////
    // No need of split
    ////
    res.push_back(s);
    return res;
  }
  else{
    // Split into two wrapped intervals

    StridedWrappedRange *s1_obj = new StridedWrappedRange(x,SP_lb,width, orig_stride);
    APInt new_ub = SP_lb - ((SP_lb - x).getZExtValue() % orig_stride);
    s1_obj->setUB(new_ub);
    s1_obj->setStride(orig_stride);
    
    if(orig_stride == 0 && s1_obj->getLB() != s1_obj->getUB()) {
        s1_obj->setStride(1);
    }
    
    s1_obj->normalizeTop();
    StridedWrappedRangePtr s1(s1_obj); // [x,  0111...1]
    
    s1_obj = new StridedWrappedRange(SP_ub,y,width, orig_stride);
    
    APInt new_lb = new_ub + orig_stride;
    s1_obj->setLB(new_lb);
    s1_obj->setStride(orig_stride);
    
    if(orig_stride == 0 && s1_obj->getLB() != s1_obj->getUB()) {
        s1_obj->setStride(1);
    }
    s1_obj->normalizeTop();
    StridedWrappedRangePtr s2(s1_obj); // [1000....0, y]

    res.push_back(s1);
    res.push_back(s2);
    return res;  
    
  }
}

/// Cut both at north and south poles
std::vector<StridedWrappedRangePtr> psplitsi(const APInt &x, const APInt &y, unsigned width){

  std::vector<StridedWrappedRangePtr> res;  
  std::vector<StridedWrappedRangePtr> s1 = StridedWrappedRange::nsplit(x,y,width);

  for (std::vector<StridedWrappedRangePtr>::iterator I = s1.begin(),
	 E=s1.end() ; I!=E ; ++I){
    StridedWrappedRange *r = (*I).get();
    std::vector<StridedWrappedRangePtr> s2  = 
      StridedWrappedRange::ssplit(r->getLB(),r->getUB(),r->getLB().getBitWidth());
    // append all elements of s2 into res
    res.insert(res.end(),s2.begin(),s2.end());
  }
  return res;
}

std::vector<StridedWrappedRangePtr> strided_psplitsi(const APInt &x, const APInt &y, unsigned width, unsigned long orig_stride){

  std::vector<StridedWrappedRangePtr> res;  
  std::vector<StridedWrappedRangePtr> s1 = StridedWrappedRange::strided_nsplit(x,y,width,orig_stride);

  for (std::vector<StridedWrappedRangePtr>::iterator I = s1.begin(), E=s1.end() ; I!=E ; ++I){
    StridedWrappedRange *r = (*I).get();
    std::vector<StridedWrappedRangePtr> s2  = 
      StridedWrappedRange::strided_ssplit(r->getLB(),r->getUB(),r->getLB().getBitWidth(), r->getStride());
    // append all elements of s2 into res
    res.insert(res.end(),s2.begin(),s2.end());
  }
  return res;
}

std::vector<StridedWrappedRangePtr>  purgeZero(StridedWrappedRangePtr RPtr){
  std::vector<StridedWrappedRangePtr> purgedZeroIntervals; 
  StridedWrappedRange * R = RPtr.get();

  assert(!(R->getLB() == 0  && R->getUB() == 0) && "Interval cannot be [0,0]");

  unsigned width = R->getLB().getBitWidth();
  // Temporary wrapped interval for zero
  APInt Zero_lb(width, 0, false);          // 000...0 
  APInt Zero_ub(width, 0, false);          // 000...0 
  StridedWrappedRange Zero(Zero_lb,Zero_ub,width,0);

  if (Zero.lessOrEqual(R)){
    if (R->getLB() == 0){
      if (R->getUB() != 0){
        // Does not cross the south pole
        StridedWrappedRangePtr s(new StridedWrappedRange(R->getLB()+1,R->getUB(),width, R->getStride()));
        purgedZeroIntervals.push_back(s);
      }
    }
    else{
      if (R->getUB() == 0){
        // If interval is e.g., [1000,0000] then we keep one interval
        APInt minusOne = APInt::getMaxValue(width); // 111...1
        StridedWrappedRangePtr s(new StridedWrappedRange(R->getLB(),minusOne  ,width, R->getStride())); // [x, 111....1]
        purgedZeroIntervals.push_back(s);
      }
      else{
        // Cross the south pole: split into two intervals
        APInt plusOne(width, 1, false);              // 000...1
        APInt minusOne = APInt::getMaxValue(width); // 111...1
        StridedWrappedRangePtr s1(new StridedWrappedRange(R->getLB(),minusOne  ,width, R->getStride())); // [x, 111....1]
        StridedWrappedRangePtr s2(new StridedWrappedRange(plusOne   ,R->getUB(),width, R->getStride()));  // [000...1,  y]
        purgedZeroIntervals.push_back(s1);
        purgedZeroIntervals.push_back(s2);
      }
    }
  }
  else{  
    // No need of split
    StridedWrappedRangePtr s(new StridedWrappedRange(*R));
    purgedZeroIntervals.push_back(s);
  }

  return purgedZeroIntervals;
}

std::vector<StridedWrappedRangePtr>  
purgeZero(const std::vector<StridedWrappedRangePtr> &Vs){
  std::vector<StridedWrappedRangePtr> res;
  for (unsigned int i=0; i<Vs.size(); i++){
    std::vector<StridedWrappedRangePtr> purgedZeroIntervals = purgeZero(Vs[i]);
    res.insert(res.end(), 
	       purgedZeroIntervals.begin(), 
	       purgedZeroIntervals.end());
  }
  return res;
}
////
// End machinery for arithmetic and bitwise operations
////

StridedWrappedRange UnsignedWrappedMult(const StridedWrappedRange *Op1, 
				 const StridedWrappedRange *Op2){
				   
  StridedWrappedRange Res(*Op1);

  APInt a = Op1->getLB();
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();
  APInt d = Op2->getUB();

  bool Overflow1, Overflow2;
  APInt lb = a.umul_ov(c,Overflow1);
  APInt ub = b.umul_ov(d,Overflow2);

  if (Overflow1 || Overflow2){
    NumOfOverflows++;
    Res.makeTop();    
    return Res;
  }
  else{
    unsigned long new_stride;
    Res.setLB(lb);
    Res.setUB(ub);
    if(Op2->isSingleVal()) {
        new_stride = (unsigned long)(Op1->getStride() * c.getZExtValue());
        
    } else if(Op1->isSingleVal()) {
        new_stride = (unsigned long)(Op2->getStride() * a.getZExtValue());
    } else {
        new_stride = UtilFunctions::getLCM(Op1->getStride(), Op2->getStride());
    }
    Res.setStride(new_stride);
    return Res;  
  }
}


StridedWrappedRange SignedWrappedMult(const StridedWrappedRange *Op1, 
			       const StridedWrappedRange *Op2){
		       
  StridedWrappedRange Res(*Op1);

  APInt a = Op1->getLB();
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();
  APInt d = Op2->getUB();

  bool IsZero_a = IsMSBZeroSI(a);
  bool IsZero_b = IsMSBZeroSI(b);
  bool IsZero_c = IsMSBZeroSI(c);
  bool IsZero_d = IsMSBZeroSI(d);
  
  unsigned long new_stride;
  if(Op2->isSingleVal()) {
    if(IsZero_c) {
        new_stride = (unsigned long)(Op1->getStride() * c.getZExtValue());
    } else {
        new_stride = (unsigned long)(Op1->getStride() * c.getSExtValue());
    }
  } else if(Op1->isSingleVal()) {
    if(IsZero_a) {
        new_stride = (unsigned long)(Op2->getStride() * a.getZExtValue());
    } else {
         new_stride = (unsigned long)(Op2->getStride() * a.getSExtValue());
    }
  } else {
    new_stride = UtilFunctions::getLCM(Op1->getStride(), Op2->getStride());
  }

  // [2,5]   * [10,20]   = [20,100]
  if (IsZero_a && IsZero_b && IsZero_c && IsZero_d){
    bool Overflow1, Overflow2;
    APInt lb = a.smul_ov(c,Overflow1);
    APInt ub = b.smul_ov(d,Overflow2);
    if (!Overflow1 && !Overflow2){
      Res.setLB(lb);
      Res.setUB(ub);
      Res.setStride(new_stride);
      return Res;
    }
  }
  // [-5,-2] * [-20,-10] = [20,100]
  else if (!IsZero_a && !IsZero_b && !IsZero_c && !IsZero_d){
    bool Overflow1, Overflow2;
    APInt lb = b.smul_ov(d,Overflow1);
    APInt ub = a.smul_ov(c,Overflow2);
    if (!Overflow1 && !Overflow2){
      Res.setLB(lb);
      Res.setUB(ub);
      Res.setStride(new_stride);
      return Res;
    }
  }
  // [-10, -2] * [2, 5] = [-50,-4]
  else if (!IsZero_a && !IsZero_b && IsZero_c && IsZero_d){
    bool Overflow1, Overflow2;
    APInt lb = a.smul_ov(d,Overflow1);
    APInt ub = b.smul_ov(c,Overflow2);
    if (!Overflow1 && !Overflow2){
      Res.setLB(lb);
      Res.setUB(ub);
      Res.setStride(new_stride);
      return Res;
    }
  }
  // [2, 10] * [-5, -2] = [-50,-4]
  else if (IsZero_a && IsZero_b && !IsZero_c && !IsZero_d){
    bool Overflow1, Overflow2;
    APInt lb = b.smul_ov(c,Overflow1);
    APInt ub = a.smul_ov(d,Overflow2);
    if (!Overflow1 && !Overflow2){
      Res.setLB(lb);
      Res.setUB(ub);
      Res.setStride(new_stride);
      return Res;
    }
  }
  /*else 
    llvm_unreachable("Unsupported case!");*/

  NumOfOverflows++;  
  Res.makeTop();

  return Res;
}


bool StridedWrappedRange::minimal_common_integer_splitted(StridedWrappedRange *Op1, StridedWrappedRange *Op2, APInt *result) {
    unsigned long op1_s, op2_s;
    float x, y;
    APInt op1_l, op2_l, op1_u, op2_u;
    op1_s = Op1->getStride();
    op2_s = Op2->getStride();
    op1_l = Op1->getLB();
    op2_l = Op2->getLB();
    op1_u = Op1->getUB();
    op2_u = Op2->getUB();

  if(Op1->isSingleVal()) {
    if(Op2->isSingleVal()) {
      if(op1_l == op2_l) {
        *result = op1_l;
        return true;   
      }
    } else if(op1_l.getZExtValue() >= op2_l.getZExtValue() && op1_l.getZExtValue() <= op2_u.getZExtValue() && ((op1_l.getZExtValue() - op2_l.getZExtValue()) % op2_s == 0)) {
      *result = op1_l;
      return true;  
   }
   return false;
  }
  if(Op2->isSingleVal()) { 
    return StridedWrappedRange::minimal_common_integer_splitted(Op2, Op1, result);
  }

 // cases for no overlap
 if(op1_u.getZExtValue() < op2_l.getZExtValue() || op2_u.getZExtValue() < op1_l.getZExtValue()) {
    return false;
 }

 if((op2_l - op1_l).getZExtValue() % UtilFunctions::getGCD(op1_s, op2_s)) {
    return false;
 }
 
 assert(Op1->getStride() != 0);

 if(UtilFunctions::diophantineNaturalSolution(-(long)(op1_l.getZExtValue() - op2_l.getZExtValue()), (long)op1_s, -(long)op2_s, &x, &y)) {
    long long_val;
    long_val = ((long)(x*op1_s) + (long)op1_l.getZExtValue());
    //width of LB or UB
    APInt first_int(Op1->getWidth(), long_val);
    if(first_int.uge(op1_l) && first_int.ule(op1_u) && first_int.uge(op2_l) && first_int.ule(op2_u)) {
        *result = first_int;
        return true;
    }
 }
 return false;

}

bool StridedWrappedRange::minimal_common_integer(StridedWrappedRange *Op1, StridedWrappedRange *Op2, APInt *result) {
    std::vector<StridedWrappedRangePtr> op1_ssplitted, op2_ssplitted, temp;
    unsigned long op1_size, op2_size;

    op1_ssplitted = strided_ssplit(Op1->getLB(), Op1->getUB(), Op1->getWidth(), Op1->getStride());
    op2_ssplitted = strided_ssplit(Op2->getLB(), Op2->getUB(), Op1->getWidth(), Op2->getStride());
    
    // swap
    if(op1_ssplitted.size() == 1 && op2_ssplitted.size() == 2) {
        temp = op1_ssplitted;
        op1_ssplitted = op2_ssplitted;
        op2_ssplitted = temp;
    }
    
    op1_size = op1_ssplitted.size();
    op2_size = op2_ssplitted.size();
    
    if(op1_size == 1 && op2_size == 1) {
        return StridedWrappedRange::minimal_common_integer_splitted(Op1, Op2, result);
    }
    APInt int0, int1;
    bool int0_valid, int1_valid;
    if(op1_size == 2 && op2_size == 1) {
        int0_valid = StridedWrappedRange::minimal_common_integer_splitted(op1_ssplitted.front().get(), op2_ssplitted.front().get(), &int0);
        int1_valid = StridedWrappedRange::minimal_common_integer_splitted(op1_ssplitted.back().get(), op2_ssplitted.front().get(), &int1);
    }
    else {
        int0_valid = StridedWrappedRange::minimal_common_integer_splitted(op1_ssplitted.front().get(), op2_ssplitted.front().get(), &int0);
        int1_valid = StridedWrappedRange::minimal_common_integer_splitted(op1_ssplitted.back().get(), op2_ssplitted.back().get(), &int1);
    }
    
    *result = int0;
    
    if(!int0_valid) {
        *result = int1;
        return int1_valid;
    }
    
    return int0_valid;
    
}

void StridedWrappedRange::WrappedMultiplication(StridedWrappedRange *LHS,
					  const StridedWrappedRange *Op1, 
					  const StridedWrappedRange *Op2){
  // Trivial case
  if (Op1->IsZeroRange() || Op2->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    LHS->setStride(0);
    return;
  }
  
  // General case: south pole and north pole cuts, meet the signed and
  // unsigned operation for each element of the Cartesian product and
  // then lubbing them
  std::vector<StridedWrappedRangePtr> s1 = 
    strided_psplitsi(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), Op1->getStride());
  std::vector<StridedWrappedRangePtr> s2 = 
    strided_psplitsi(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth(), Op2->getStride());

  LHS->makeBot();
  if(Op1->isSingleVal() && Op2->isSingleVal()) {
      LHS->resetBottomFlag();
      LHS->resetTopFlag();
      LHS->setStride(0);
      LHS->setLB(Op1->getLB() * Op2->getLB());
      LHS->setUB(Op1->getUB() * Op2->getUB());
  }
  std::vector<StridedWrappedRangePtr> allranges;
  typedef std::vector<StridedWrappedRangePtr>::iterator It;
  for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      StridedWrappedRange Tmp1 = UnsignedWrappedMult((*I1).get(),(*I2).get());
      StridedWrappedRange Tmp2 = SignedWrappedMult((*I1).get(),(*I2).get());
      std::vector<StridedWrappedRangePtr> curr_ranges = StridedWrappedRange::MultiValueIntersection(&Tmp1, &Tmp2);
      allranges.insert(allranges.end(), curr_ranges.begin(), curr_ranges.end());
    }
  }
  
  std::vector<AbstractValue*> Rs;
  std::transform(allranges.begin(), allranges.end(), 
		 std::back_inserter(Rs), 
		 convertPtrValToAbs);
		 
  StridedWrappedRange result_val(*LHS);
  
  if(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val)) {
    LHS->WrappedRangeAssign(&result_val);
  }
}

void StridedWrappedRange::AdjustStride() {
    if(!this->IsTop() && !this->isBot()) {
        if(this->getLB() == this->getUB()) {
            this->setStride(0);
        } else {
            this->setStride(1);
        }
    }
}


// Pre: Divisor does not contain the interval [0,0] and does not
// straddle the poles.
StridedWrappedRange WrappedUnsignedDivision(StridedWrappedRange const *Dividend, 
				     StridedWrappedRange const *Divisor){

  StridedWrappedRange Res(*Dividend);
  APInt a = Dividend->getLB();
  APInt b = Dividend->getUB();
  APInt c = Divisor->getLB();
  APInt d = Divisor->getUB();
  
  Res.setLB(a.udiv(d));
  Res.setUB(b.udiv(c));
  Res.AdjustStride();
  return Res;
}

// Pre: Divisor does not contain the interval [0,0] and does not
// straddle the poles.
StridedWrappedRange WrappedSignedDivision(StridedWrappedRange const *Dividend, 
				   StridedWrappedRange const *Divisor, 
				   bool & IsOverflow){

  IsOverflow = false;

  StridedWrappedRange Res(*Dividend);
  APInt a = Dividend->getLB();
  APInt b = Dividend->getUB();
  APInt c = Divisor->getLB();
  APInt d = Divisor->getUB();

  bool IsZero_a = IsMSBZeroSI(a);
  bool IsZero_c = IsMSBZeroSI(c);

  if (IsZero_a && IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(a.sdiv_ov(d,IsOverflow1));
    Res.setUB(b.sdiv_ov(c,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
    Res.AdjustStride();
    return Res;
  }
  else if (!IsZero_a && !IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(b.sdiv_ov(c,IsOverflow1));
    Res.setUB(a.sdiv_ov(d,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
    Res.AdjustStride();
    return Res;
  }
  else if (IsZero_a && !IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(b.sdiv_ov(d,IsOverflow1));
    Res.setUB(a.sdiv_ov(c,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
    Res.AdjustStride();
    return Res;
  }
  else if (!IsZero_a && IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(a.sdiv_ov(c,IsOverflow1));
    Res.setUB(b.sdiv_ov(d,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
    Res.AdjustStride();
    return Res;
  }

  llvm_unreachable("This should be unreachable");
}

void StridedWrappedRange::WrappedDivision(StridedWrappedRange *LHS, 
				   const StridedWrappedRange *Dividend, 
				   const StridedWrappedRange *Divisor, 
				   bool IsSignedDiv){
  // Trivial cases
  if (Dividend->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    LHS->setStride(0);
    return;
  }
  if (Divisor->IsZeroRange()){
    LHS->makeBot();
    return;
  }
  
  std::vector<AbstractValue*> Rs;

  if (IsSignedDiv){
    // General case: south pole and north pole cuts and compute signed
    // operation for each element of the Cartesian product and then
    // lubbing them. Note that we make sure that [0,0] is removed from
    // the divisor.
    std::vector<StridedWrappedRangePtr> s1 = 
      strided_psplitsi(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth(), Dividend->getStride());
    std::vector<StridedWrappedRangePtr> s2 = 
      purgeZero(strided_psplitsi(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth(), Divisor->getStride()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");

    typedef std::vector<StridedWrappedRangePtr>::iterator It;
    LHS->makeBot();
    
    bool is_top = false;
      
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
       	bool IsOverflow;
	      StridedWrappedRange Tmp = WrappedSignedDivision((*I1).get(),(*I2).get(),
						 IsOverflow);
  	    if (IsOverflow){
  	      NumOfOverflows++;
  	      LHS->makeTop();
          is_top = true;
  	      break;
  	    }
  	    StridedWrappedRange *new_val = new StridedWrappedRange(Tmp);
  	    Rs.push_back(cast<AbstractValue>(new_val));
      }
    }
    
    if(!is_top) {
      StridedWrappedRange result_val(*LHS);
      assert(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val) && "least upper bound failed in WrappedSignedDivision");
      LHS->WrappedRangeAssign(&result_val);
    }
    
  }
  else{
    // General case: south pole cut and compute unsigned operation for
    // each element of the Cartesian product and then lubbing
    // them. Note that we make sure that [0,0] is removed from the
    // divisor.
    std::vector<StridedWrappedRangePtr> s1 = 
      strided_ssplit(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth(), Dividend->getStride());
    std::vector<StridedWrappedRangePtr> s2 = 
      purgeZero(strided_ssplit(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth(), Divisor->getStride()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");
    LHS->makeBot();  
    typedef std::vector<StridedWrappedRangePtr>::iterator It;
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	      StridedWrappedRange Tmp = WrappedUnsignedDivision((*I1).get(),(*I2).get());
	      StridedWrappedRange *new_val = new StridedWrappedRange(Tmp);
  	    Rs.push_back(cast<AbstractValue>(new_val));
      }
    }
    
    StridedWrappedRange result_val(*LHS);
    assert(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val) && "least upper bound failed in WrappedUnSignedDivision");
    LHS->WrappedRangeAssign(&result_val);
  }
  
  // free all elements
  unsigned long i = 0;
  while(i<Rs.size()) {
      delete Rs[i];
      i++;
  }
    
  Rs.clear();
}


void StridedWrappedRange::
  WrappedRem(StridedWrappedRange *LHS, 
	     const StridedWrappedRange *Dividend,  const StridedWrappedRange *Divisor, 
	     bool IsSignedRem){ 

  // Trivial cases
  if (Dividend->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    LHS->setStride(0);
    return;
  }
  if (Divisor->IsZeroRange()){
    LHS->makeBot();
    return;
  }
  std::vector<AbstractValue*> Rs;
  
  if (IsSignedRem){
    // General case: south pole cut and compute unsigned operation for
    // each element of the Cartesian product and then lubbing
    // them. Note that we make sure that [0,0] is removed from the
    // divisor.
    std::vector<StridedWrappedRangePtr> s1 = 
      strided_ssplit(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth(), Dividend->getStride());

    std::vector<StridedWrappedRangePtr> s2 = 
      purgeZero(strided_ssplit(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth(), Divisor->getStride()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");
    LHS->makeBot();  
    typedef std::vector<StridedWrappedRangePtr>::iterator It;
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	APInt a = (*I1).get()->getLB();
	APInt b = (*I1).get()->getUB();
	APInt c = (*I2).get()->getLB();
	APInt d = (*I2).get()->getUB();

	bool IsZero_a = IsMSBZeroSI(a);
	bool IsZero_c = IsMSBZeroSI(c);

	unsigned width = b.getBitWidth();
	APInt lb; APInt ub;
	if (IsZero_a && IsZero_c){ 
	  // [0,d-1]
	  lb = APInt(width, 0, false); 
	  ub = d-1;
	}
	else if (IsZero_a && !IsZero_c){
	  // [0,-c-1]
	  lb = APInt(width, 0, false); 
	  ub = -c-1;
	}
	else if (!IsZero_a && IsZero_c){
	  // [-d+1,0]
	  lb = -d+1;
	  ub = APInt(width, 0, false); 
	}
	else if (!IsZero_a && !IsZero_c){
	  // [c+1,0]
	  lb = c+1;
	  ub = APInt(width, 0, false); 
	}
	else
	  llvm_unreachable("This should be unreachable!");

	StridedWrappedRange tmp(lb,ub,width, 1);	 
	//LHS->join(&tmp);
	StridedWrappedRange *new_val = new StridedWrappedRange(tmp);
  	Rs.push_back(cast<AbstractValue>(new_val));
      }
    }
  }
  else{
    // General case: south pole cut and compute unsigned operation for
    // each element of the Cartesian product and then lubbing
    // them. Note that we make sure that [0,0] is removed from the
    // divisor.
    std::vector<StridedWrappedRangePtr> s1 = 
      strided_ssplit(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth(), Dividend->getStride());
    std::vector<StridedWrappedRangePtr> s2 = 
      purgeZero(strided_ssplit(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth(), Divisor->getStride()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");
    LHS->makeBot();  
    typedef std::vector<StridedWrappedRangePtr>::iterator It;
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	      APInt d  = (*I2).get()->getUB();
	      APInt lb = APInt(width, 0, false);
	      APInt ub = d - 1;
 	      unsigned width = d.getBitWidth();
	      StridedWrappedRange tmp(lb,ub,width,1);
	      StridedWrappedRange *new_val = new StridedWrappedRange(tmp);
        Rs.push_back(cast<AbstractValue>(new_val));
      }
    }
  }
  
  StridedWrappedRange result_val(*LHS);
  
  assert(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val) && "least upper bound failed in Rem");
  LHS->WrappedRangeAssign(&result_val);
  
  // free all elements
  unsigned long i = 0;
  while(i<Rs.size()) {
      delete Rs[i];
      i++;
  }
    
  Rs.clear();
      
}

void StridedWrappedRange::
  WrappedPlus(StridedWrappedRange *LHS,
	      const StridedWrappedRange *Op1, const StridedWrappedRange *Op2){
  //  [a,b] + [c,d] = [a+c,b+d] if no overflow
  //  top                       otherwise
  if (IsWrappedOverflow_AddSubSI(Op1->getLB(),Op1->getUB(),
			       Op2->getLB(),Op2->getUB())){
    NumOfOverflows++;
    LHS->makeTop();
    return;
  }
  
  // Addition in APInt performs modular arithmetic
  LHS->setLB(Op1->getLB() + Op2->getLB());
  LHS->setUB(Op1->getUB() + Op2->getUB());
  unsigned long new_s = UtilFunctions::getGCD(Op1->getStride(), Op2->getStride());
 
  LHS->setStride(new_s);
}

void StridedWrappedRange::
  WrappedMinus(StridedWrappedRange *LHS,
	       const StridedWrappedRange *Op1, const StridedWrappedRange *Op2){
    //  [a,b] - [c,d] = [a-d,b-c] if no overflow
    //  top                       otherwise
    if (IsWrappedOverflow_AddSubSI(Op1->getLB(),Op1->getUB(),
				 Op2->getLB(),Op2->getUB())){
      NumOfOverflows++;
      LHS->makeTop();
      return;
    }
    
    /// minus in APInt performs modular arithmetic
    LHS->setLB(Op1->getLB() - Op2->getUB());
    LHS->setUB(Op1->getUB() - Op2->getLB());
    unsigned long new_s = UtilFunctions::getGCD(Op1->getStride(), Op2->getStride());
    LHS->setStride(new_s);
}      


/// Perform the transfer function for binary arithmetic operations.
AbstractValue* StridedWrappedRange::
visitArithBinaryOp(AbstractValue *V1,AbstractValue *V2,
		   unsigned OpCode, const char *OpCodeName){

  StridedWrappedRange *Op1 = cast<StridedWrappedRange>(V1);
  StridedWrappedRange *Op2 = cast<StridedWrappedRange>(V2);
  StridedWrappedRange *LHS = new StridedWrappedRange(*this);

#ifdef EVAL
  DEBUG(dbgs() << "\t [RESULT] ");
  DEBUG(Op1->printRange(dbgs()));
  DEBUG(dbgs() << " " << OpCodeName << " ");
  DEBUG(Op2->printRange(dbgs()));
  DEBUG(dbgs() << " = ");
#endif

  /// First simple cases: bottom, top, etc
  if (Op1->isBot() || Op2->isBot()){
    LHS->makeBot();
    goto END;
  }
  if (Op1->IsTop() || Op2->IsTop()){
    LHS->makeTop();
    goto END;
  }
  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the arithmetic operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  switch (OpCode){
  case Instruction::Add:
    WrappedPlus(LHS,Op1,Op2);
    break;
  case Instruction::Sub:
    WrappedMinus(LHS,Op1,Op2);
    break;
  case Instruction::Mul:
    WrappedMultiplication(LHS, Op1, Op2);
    break;
  case Instruction::UDiv:
    WrappedDivision(LHS, Op1, Op2, false);
    break;
  case Instruction::SDiv:
    WrappedDivision(LHS, Op1, Op2, true);
    break;
  case Instruction::URem:
    WrappedRem(LHS, Op1, Op2, false);
    break;
  case Instruction::SRem:
    WrappedRem(LHS, Op1, Op2, true);
    break;
  default:
#ifdef EVAL
    dbgs() << OpCodeName << "\n";
#endif
    llvm_unreachable("Arithmetic operation not implemented");
  } // end switch

 END:
  LHS->normalizeTop();
#ifdef EVAL
  DEBUG(LHS->printRange(dbgs()));
  DEBUG(dbgs() << "\n");
#endif

  return LHS;
}

// Pre: Operand is not bottom
// LHS is an in/out argument
void Truncate(StridedWrappedRange *&LHS, StridedWrappedRange *Operand, unsigned k){
  APInt a= Operand->getLB();
  APInt b= Operand->getUB();
  assert(a.getBitWidth() == b.getBitWidth());
  assert(k < a.getBitWidth());
  uint64_t k_max_int = ((uint64_t)1 << k) - 1;
  if ( (a.ashr(k) == b.ashr(k)) &&
           SILex_LessOrEqual(a.trunc(k),b.trunc(k))){
    LHS->setLB(a.trunc(k));
    LHS->setUB(b.trunc(k));
    LHS->setStride(Operand->getStride() & ((2 << k) -1 ));
  }
  // APInt will wraparound if +1 overflow so == is modular arithmetic
  else if ( (a.ashr(k)+1 == b.ashr(k)) &&
	        (!SILex_LessOrEqual(a.trunc(k),b.trunc(k)))){
    LHS->setLB(a.trunc(k));
    LHS->setUB(b.trunc(k));
    LHS->setStride(Operand->getStride() & ((2 << k) -1 ));
  }
  else{
    APInt str_val(a.getBitWidth(), Operand->getStride());
    unsigned num_trailing_zeros = str_val.countTrailingZeros();

    if(k > num_trailing_zeros) {
        uint64_t new_mask = (((uint64_t)1 << num_trailing_zeros) - 1);
        uint64_t new_lower = a.getZExtValue() & new_mask;
        unsigned long new_stride = (1 << num_trailing_zeros);
        APInt max_up = APInt::getMaxValue(a.getBitWidth());
        unsigned long temp_k = (max_up.getZExtValue() - new_lower) / new_stride;
        uint64_t new_upper = new_stride * temp_k + new_lower;
        APInt lb = APInt(k, new_lower);
        APInt ub = APInt(k, new_upper);
        LHS->setLB(lb);
        LHS->setUB(ub);
        LHS->setStride(new_stride);
    } else {
        uint64_t tok_mask = (((uint64_t)1 << k) - 1);
        uint64_t new_lower = a.getZExtValue() & tok_mask;
        uint64_t new_upper = b.getZExtValue() & tok_mask;
        APInt lb = APInt(k, new_lower);
        APInt ub = APInt(k, new_upper);
        LHS->setLB(lb);
        LHS->setUB(ub);
          LHS->setStride(0);
          assert(lb == ub);
      }
  }
}
 
/// Perform the transfer function for casting operations.
AbstractValue* StridedWrappedRange::
visitCast(Instruction &I, 
	  AbstractValue * V, TBool *TB, bool){

  // Very special case: convert TBool to WrappedRange
  StridedWrappedRange *RHS = NULL;
  if (!V){
    // Special case if the source is a Boolean Flag    
    assert(TB && "ERROR: visitCat assumes that TB != NULL");
    RHS = new StridedWrappedRange(I.getOperand(0), TB);
  }
  else{
    // Common case
    RHS = cast<StridedWrappedRange>(V);    
    assert(!TB && "ERROR: some inconsistency found in visitCast");
  }
  StridedWrappedRange *LHS = new StridedWrappedRange(*this);

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the casting operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  // Check some possible errors
  unsigned srcWidth,destWidth;  
  const Type * srcTy  =  I.getOperand(0)->getType();
  const Type * destTy =  I.getType();
  BaseRange::
    checkCastingOp(srcTy,srcWidth,destTy,destWidth,I.getOpcode(),RHS->getWidth()); 
		   
  /// Start doing casting: change width
  LHS->setZeroAndChangeWidth(destWidth);          

  /// Simple cases first: bottom and top
  if (RHS->isBot())
    LHS->makeTop(); // be conservative
  else if (RHS->IsTop())
    LHS->makeTop();
  else{
    switch(I.getOpcode()) {
    case Instruction::Trunc:
      {
	unsigned k;
	Utilities::getIntegerWidth(I.getType(),k);      
	Truncate(LHS, RHS,k);
      }
      break;
    case Instruction::ZExt:
      {
	unsigned k;
	Utilities::getIntegerWidth(I.getType(),k);
	// **SOUTH POLE SPLIT** and compute signed extension for each of
	// two elements and then lubbing them
	std::vector<StridedWrappedRangePtr> s = 
	  strided_ssplit(RHS->getLB(), RHS->getUB(), RHS->getLB().getBitWidth(), RHS->getStride());
	StridedWrappedRange Tmp(*LHS);
	LHS->makeBot();
	std::vector<AbstractValue*> Rs;  
	for (std::vector<StridedWrappedRangePtr>::iterator 
	       I=s.begin(), E=s.end(); I!=E; ++I){
	  APInt a = (*I).get()->getLB();
	  APInt b = (*I).get()->getUB();
	  Tmp.setLB(a.zext(k));
	  Tmp.setUB(b.zext(k));
	  Tmp.setStride((*I).get()->getStride());
	  StridedWrappedRange *new_val = new StridedWrappedRange(Tmp);
      Rs.push_back(cast<AbstractValue>(new_val));
	}
	
	StridedWrappedRange result_val(*LHS);
  
      assert(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val) && "least upper bound failed in SExt");
      LHS->WrappedRangeAssign(&result_val);
      
      // free all elements
      unsigned long i = 0;
      while(i<Rs.size()) {
          delete Rs[i];
          i++;
      }
        
      Rs.clear();
    }
      break;
    case Instruction::SExt:  
      {  
        unsigned k;
        Utilities::getIntegerWidth(I.getType(),k);
        // **NORTH POLE SPLIT** and compute signed extension for each of
        // the two elements and then lubbing them
        std::vector<StridedWrappedRangePtr> s =
          strided_nsplit(RHS->getLB(), RHS->getUB(), RHS->getLB().getBitWidth(), RHS->getStride());
        StridedWrappedRange Tmp(*LHS);
        LHS->makeBot();
        std::vector<AbstractValue*> Rs;
        typedef std::vector<StridedWrappedRangePtr>::iterator It;

        for (It I=s.begin(), E=s.end(); I!=E; ++I){
          APInt a = (*I).get()->getLB();
          APInt b = (*I).get()->getUB();
          Tmp.setLB(a.sext(k));
          Tmp.setUB(b.sext(k));
          Tmp.setStride((*I).get()->getStride());
          // GeneralizedJoin does not help since we have at most two
          // intervals to be joined.
          //LHS->join(&Tmp);
          StridedWrappedRange *new_val = new StridedWrappedRange(Tmp);
            Rs.push_back(cast<AbstractValue>(new_val));
        }

        StridedWrappedRange result_val(*LHS);

        assert(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val) && "least upper bound failed in SExt");
        LHS->WrappedRangeAssign(&result_val);

        // free all elements
        unsigned long i = 0;
        while(i<Rs.size()) {
            delete Rs[i];
            i++;
        }

        Rs.clear();
      }
      break;    
    default:; // bitcast are non-op
    } // end switch
  }
  
  if (!V) delete RHS;
   LHS->normalizeTop();
#ifdef EVAL
  DEBUG(dbgs() << "\t[RESULT]");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");
#endif

  return LHS;
}

StridedWrappedRange StridedWrappedRange::StridedLogicalBitwiseOr(StridedWrappedRange *Op1, StridedWrappedRange *Op2) {
  StridedWrappedRange Result(*Op1);
  std::vector<StridedWrappedRangePtr> s1 =
    strided_ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), Op1->getStride());
  std::vector<StridedWrappedRangePtr> s2 = 
    strided_ssplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth(), Op2->getStride());

  Result.makeBot(); 
  std::vector<AbstractValue*> Rs; 
  typedef std::vector<StridedWrappedRangePtr>::iterator It;
   
  for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      APInt lb; APInt ub;
      unimelb::unsignedOr((*I1).get(), (*I2).get(), lb, ub);
	  StridedWrappedRange Tmp(lb, ub, Op1->getLB().getBitWidth());

	  unsigned long s_t, new_stride;
	  unsigned long i1_ntz, i2_ntz;
	  i1_ntz = unimelb::NumContZeros((*I1).get()->getStride());
	  i2_ntz = unimelb::NumContZeros((*I2).get()->getStride());

	  if((*I1).get()->isSingleVal()) {
	    s_t = i2_ntz;
	  } else if((*I2).get()->isSingleVal()) {
	    s_t = i1_ntz;
	  } else {
	    s_t = (i1_ntz<i2_ntz)?i1_ntz:i2_ntz;
	  }
	  
	  if((*I1).get()->isSingleVal() && ((*I1).get()->getLB().getZExtValue() == 0)) {
	    new_stride = (*I2).get()->getStride();  
	  } else if((*I2).get()->isSingleVal() && ((*I2).get()->getLB().getZExtValue() == 0)) {
	    new_stride = (*I1).get()->getStride();  
	  } else {
	    new_stride = ((unsigned long)1) << s_t;
	  }
	  
	  if(Tmp.getLB() == Tmp.getUB()) {
	    Tmp.setStride(0);
	  } else {
	    Tmp.setStride(new_stride);
	  }
	  
	  StridedWrappedRange *new_val = new StridedWrappedRange(Tmp);
      Rs.push_back(cast<AbstractValue>(new_val));
    }
  }
  StridedWrappedRange result_val(Result);
  
  assert(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val) && "least upper bound failed in StridedLogicalOr");
  Result.WrappedRangeAssign(&result_val);
      
  // free all elements
  unsigned long i = 0;
  while(i<Rs.size()) {
      delete Rs[i];
      i++;
  }
        
  Rs.clear();
      
  return Result;
}

StridedWrappedRange StridedWrappedRange::StridedLogicalBitwiseNot(StridedWrappedRange *Op1) {
  StridedWrappedRange Result(*Op1);
  
  std::vector<StridedWrappedRangePtr> s1 =
  strided_ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), Op1->getStride());
  
  APInt lb_o, ub_o;
  lb_o = ~(Op1->getUB());
  ub_o = ~(Op1->getLB());
  Result.makeBot(); 
  std::vector<AbstractValue*> Rs; 
  typedef std::vector<StridedWrappedRangePtr>::iterator It;
   
  for (It I1 = s1.begin(), E1 = s1.end(); I1 != E1; ++I1){
    APInt lb; APInt ub;
    ub = ub_o;//~((*I1).get()->getLB());
    lb = lb_o;//~((*I1).get()->getUB());
    
    StridedWrappedRange Tmp(lb, ub, lb.getBitWidth());
    Tmp.setStride(Op1->getStride());//(*I1).get()->getStride());
    StridedWrappedRange *new_val = new StridedWrappedRange(Tmp);
    Rs.push_back(cast<AbstractValue>(new_val));
  }
  StridedWrappedRange result_val(Result);
  
  assert(StridedWrappedRange::StridedGeneralizedJoin(Rs,&result_val) && "least upper bound failed in StridedLogicalBitwiseNot");
  Result.WrappedRangeAssign(&result_val);
      
  // free all elements
  unsigned long i = 0;
  while(i<Rs.size()) {
      delete Rs[i];
      i++;
  }
        
  Rs.clear();
      
  return Result;
}

void StridedWrappedRange::WrappedLogicalBitwise(StridedWrappedRange *LHS, 
					 StridedWrappedRange *Op1, StridedWrappedRange *Op2,
					 unsigned Opcode){
 
  // General case: **SOUTH POLE SPLIT** and compute operation for each
  // of the elements and then lubbing them

  StridedWrappedRange temp_result(*Op1);

  LHS->makeBot(); 

  switch(Opcode) {
    case Instruction::Or:
        {
            temp_result = StridedWrappedRange::StridedLogicalBitwiseOr(Op1, Op2);
            LHS->WrappedRangeAssign(&temp_result);
        }
        break;
    case Instruction::And:
        {
            StridedWrappedRange op1_not(*Op1), op2_not(*Op2);
            op1_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op1);
            op2_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op2);
            
            temp_result = StridedWrappedRange::StridedLogicalBitwiseOr(&op1_not, &op2_not);
            temp_result = StridedWrappedRange::StridedLogicalBitwiseNot(&temp_result);
            LHS->WrappedRangeAssign(&temp_result);
        }
        break;
    case Instruction::Xor:
        {
            StridedWrappedRange op1_not(*Op1), op2_not(*Op2), first_op(*Op1), second_op(*Op2);
            op1_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op1);
            op2_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op2);
            
            first_op = StridedWrappedRange::StridedLogicalBitwiseOr(&op1_not, Op2);
            first_op = StridedWrappedRange::StridedLogicalBitwiseNot(&first_op);
            
            second_op = StridedWrappedRange::StridedLogicalBitwiseOr(Op1, &op2_not);
            second_op = StridedWrappedRange::StridedLogicalBitwiseNot(&second_op);
            
            temp_result = StridedWrappedRange::StridedLogicalBitwiseOr(&first_op, &second_op);
            LHS->WrappedRangeAssign(&temp_result);
            
        }
        break;
    default:
        llvm_unreachable("Unexpected instruction");
  }
  
}

StridedWrappedRange StridedWrappedRange::StridedLShr(StridedWrappedRange *Op, uint64_t val) {
    StridedWrappedRange Result(*Op);
    unsigned long ntz;
    Result.makeBot();
    if(val <= Op->getLB().getBitWidth()) {
        StridedWrappedRange temp_result(Op->getLB(), Op->getLB(), Op->getLB().getBitWidth(), 0);
        std::vector<StridedWrappedRangePtr> s1 = 
        strided_ssplit(Op->getLB(), Op->getUB(), Op->getLB().getBitWidth(), Op->getStride());
        typedef std::vector<StridedWrappedRangePtr>::iterator It;
        for (It I1 = s1.begin(), E1 = s1.end(); I1 != E1; ++I1) {
            APInt lb((*I1).get()->getLB());
            APInt ub((*I1).get()->getUB());
            APInt unsig_lb(lb.getBitWidth(), lb.getZExtValue(), false);
            APInt unsig_ub(ub.getBitWidth(), ub.getZExtValue(), false);
            
            APInt new_lb = unsig_lb.lshr((unsigned)val);
            APInt new_ub = unsig_ub.lshr((unsigned)val);
            unsigned long new_stride, curr_stride;
            curr_stride = ((*I1).get()->getStride()) >> val;
            ntz = unimelb::NumContZeros((*I1).get()->getStride()); 
            if (ntz >= val) {
                new_stride = curr_stride;
            } else {
               new_stride = 1;
            } 
            //new_stride = (curr_stride>1)?curr_stride:1;
            temp_result.setLB(new_lb);
            temp_result.setUB(new_ub);
            temp_result.setStride(new_stride);
            temp_result.normalizeTop();
            Result.join(&temp_result);
        }
    } else {
        Result.makeTop();
    }
    
    return Result;
}

StridedWrappedRange StridedWrappedRange::StridedAShr(StridedWrappedRange *Op, uint64_t val) {
    StridedWrappedRange Result(*Op);
   unsigned long ntz; 
    Result.makeBot();
    if(val <= Op->getLB().getBitWidth()) {
        //StridedWrappedRange temp_result(*Op);
        StridedWrappedRange temp_result(Op->getLB(), Op->getLB(), Op->getLB().getBitWidth(), 0);
        std::vector<StridedWrappedRangePtr> s1 = 
        strided_nsplit(Op->getLB(), Op->getUB(), Op->getLB().getBitWidth(), Op->getStride());
        typedef std::vector<StridedWrappedRangePtr>::iterator It;
        for (It I1 = s1.begin(), E1 = s1.end(); I1 != E1; ++I1) {        
            APInt new_lb = (*I1).get()->getLB().ashr((unsigned)val);
            APInt new_ub = (*I1).get()->getUB().ashr((unsigned)val);
            unsigned long new_stride, curr_stride;
            curr_stride = ((*I1).get()->getStride()) >> val;
            //new_stride = (curr_stride>1)?curr_stride:1; 
            ntz = unimelb::NumContZeros((*I1).get()->getStride()); 
            if (ntz >= val) {
                new_stride = curr_stride;
            } else {
               new_stride = 1;
            } 
            temp_result.setLB(new_lb);
            temp_result.setUB(new_ub);
            temp_result.setStride(new_stride);
            temp_result.normalizeTop();
            Result.join(&temp_result);
        }
    } else {
        Result.makeTop();
    }
    
    return Result;
}

StridedWrappedRange StridedWrappedRange::StridedShl(StridedWrappedRange *Op, uint64_t val) {
    StridedWrappedRange Result(*Op);
   unsigned long ntz; 
    Result.makeBot();
    if(val <= Op->getLB().getBitWidth()) {
        //StridedWrappedRange temp_result(*Op);
        StridedWrappedRange temp_result(Op->getLB(), Op->getLB(), Op->getLB().getBitWidth(), 0);
        std::vector<StridedWrappedRangePtr> s1 = 
        strided_ssplit(Op->getLB(), Op->getUB(), Op->getLB().getBitWidth(), Op->getStride());
        typedef std::vector<StridedWrappedRangePtr>::iterator It;
        for (It I1 = s1.begin(), E1 = s1.end(); I1 != E1; ++I1) {        
            APInt new_lb(Op->getLB());
            APInt new_ub(Op->getUB());
        
            new_lb = new_lb << (unsigned)val;
            new_ub = new_ub << (unsigned)val;
            unsigned long new_stride, curr_stride;
            curr_stride = ((*I1).get()->getStride()) << val;
            new_stride = (curr_stride>1)?curr_stride:1;
            if (new_lb == new_ub) {
                new_stride = 0;
            } 
            temp_result.setLB(new_lb);
            temp_result.setUB(new_ub);
            temp_result.setStride(new_stride);
            temp_result.normalizeTop();
            Result.join(&temp_result);
        }
    } else {
        Result.makeTop();
    }
return Result;
}


void StridedWrappedRange::StridedWrappedBitwiseShitfs(StridedWrappedRange *LHS, StridedWrappedRange *Operand, StridedWrappedRange *Shift, unsigned Opcode) {
    LHS->makeBot(); 
    
    std::vector<StridedWrappedRangePtr> s1 = 
    strided_ssplit(Shift->getLB(), Shift->getUB(), Shift->getLB().getBitWidth(), Shift->getStride());
    
    StridedWrappedRange tmpResult(*Operand);
    typedef std::vector<StridedWrappedRangePtr>::iterator It;
    for (It I1 = s1.begin(), E1 = s1.end(); I1 != E1; ++I1) {
        uint64_t lower_val, upper_val;
        unsigned long incr = (*I1).get()->getStride();
        lower_val = ((*I1).get()->getLB()).getZExtValue();
        upper_val = ((*I1).get()->getUB()).getZExtValue();
        assert(lower_val <= upper_val);
        //Sanity, for constants, incr will be 0.
        // Just making sure that underlying while loop will terminate.
        if(!incr) {
            incr += 1;
        }
        while(lower_val <= upper_val) {
            switch(Opcode) {
                case Instruction::Shl:
                    {
                        tmpResult = StridedWrappedRange::StridedShl(Operand, lower_val);
                        LHS->join(&tmpResult);
                    }
                    break;
                case Instruction::LShr:
                    {
                        tmpResult = StridedWrappedRange::StridedLShr(Operand, lower_val);
                        LHS->join(&tmpResult);
                    }
                    break;
                case Instruction::AShr:
                    {
                        tmpResult = StridedWrappedRange::StridedAShr(Operand, lower_val);
                        LHS->join(&tmpResult);
                    }
                    break;
                default:
                    llvm_unreachable("Unexpected instruction");
              
            }
            lower_val += incr;
            if(LHS->IsTop()) {
                break;
            }
        }
        if(LHS->IsTop()) {
                break;
        }
    }
}

/// Perform the transfer function for bitwise  operations. 
AbstractValue* StridedWrappedRange::
visitBitwiseBinaryOp(AbstractValue * V1, 
		     AbstractValue * V2, 
		     const Type * Op1Ty, const Type * Op2Ty, 
		     unsigned OpCode   , const char * OpCodeName){
  
  StridedWrappedRange *Op1 = cast<StridedWrappedRange>(V1);
  StridedWrappedRange *Op2 = cast<StridedWrappedRange>(V2);
  StridedWrappedRange *LHS = new StridedWrappedRange(*this);

  // Be careful: top can be improved. Therefore, don't return directly
  // top if one of the operand is top

  // During narrowing values that were top may not be. We need to
  // reset the top flag by hand (gross!)
  LHS->resetTopFlag();
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the bitwise operation returns bottom then the bottom
  // flag will turn on again.
  LHS->resetBottomFlag();

  switch(OpCode){
  case Instruction::And:
  case Instruction::Xor:
  case Instruction::Or:
    if (Op1->isBot() || Op2->isBot()){
      LHS->makeTop(); // be conservative here
      //LHS->makeBot();
      break;
    }
    /////////////////////////////////////////////////////////////////
    // Top is special for logical bitwise because we can go down in
    // the poset from it.
    /////////////////////////////////////////////////////////////////
    if (Op1->IsTop() && Op2->IsTop()){
      LHS->makeTop();
    }      
    else if (Op1->IsTop()){
      StridedWrappedRange Tmp(*Op1);
      Tmp.resetTopFlag();
      // NOTE: Here we can create either [0..0,1...1] or
      // [10...0,01...1]. The former is more efficient because it
      // avoids a cut at SP later on. However, depending on how join
      // resolves non-deterministic cases the latter may be more
      // precise. 
      // 
      // E.g., consider 4-bit intervals top or [0010,0010] and
      // then a signed extension to 5 bits.
      //
      // [0000,1111] or [0010,0010] = [0010,1111]
      // after signed extension we get [00010,11111]
      //
      // [1000,0111] or [0010,0010] can produce either [0010,1111] or
      // [1010,0111] depending on the join. If we choose [1010,0111]
      // then after signed extension we get [11010,00111] which is
      // more precise than [00010,11111] !!
      //
      // We create here [0..0,1...1] which doesn't cross SP.
      // Therefore, Or,And, and XOr will not perform any cut.
      //Tmp.setLB((uint64_t) 0);
      //Tmp.setUB(APInt::getMaxValue(Tmp.getWidth()));
      // We create here [10...0,01...1] which doesn't cross NP.
      Tmp.setLB(APInt::getSignedMinValue(Tmp.getWidth()));
      Tmp.setUB(APInt::getSignedMaxValue(Tmp.getWidth()));

      WrappedLogicalBitwise(LHS, &Tmp, Op2, OpCode);
    }      
    else if (Op2->IsTop()){
      StridedWrappedRange Tmp(*Op2);
      Tmp.resetTopFlag();
      Tmp.setLB((uint64_t) 0);
      Tmp.setUB(APInt::getMaxValue(Tmp.getWidth()));
      WrappedLogicalBitwise(LHS, Op1, &Tmp,  OpCode);	  
    }      
    else 
      WrappedLogicalBitwise(LHS, Op1, Op2, OpCode);
    break;
  case Instruction::Shl: 
  case Instruction::LShr: 
  case Instruction::AShr: 
    if (Op1->isBot() || Op2->isBot()){ //be conservative here
      LHS->makeTop();
      break;
    }

    if (!checkOpWithShift(Op1,Op2)){
      LHS->makeTop();
      break;
    }

    if (Op2->IsZeroRange()){
      // If the shift is zero then the instruction is a non-op
      LHS->RangeAssign(Op1);
      break;
    }
    
    StridedWrappedBitwiseShitfs(LHS, Op1, Op2,OpCode);
    break;
  default:;
  } // end switch

  LHS->normalizeTop();
#ifdef EVAL
  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");
#endif
  return LHS;  
}


// Tests

void test_GeneralizedJoinSI(){
  {
    APInt a(8,  2,false);  APInt b(8, 10,false);
    APInt c(8,120,false);  APInt d(8,130,false);
    APInt e(8,132,false);  APInt f(8,135,false);
    APInt zero(8,0,false); 
    // Temporary constructors
    AbstractValue * R1 = dyn_cast<AbstractValue>(new StridedWrappedRange(a,b,a.getBitWidth()));
    AbstractValue * R2 = dyn_cast<AbstractValue>(new StridedWrappedRange(c,d,c.getBitWidth()));
    AbstractValue * R3 = dyn_cast<AbstractValue>(new StridedWrappedRange(e,f,e.getBitWidth()));
    std::vector<AbstractValue*> vv;
    vv.push_back(R3); vv.push_back(R2); vv.push_back(R1);
    StridedWrappedRange * Res = new StridedWrappedRange(zero,zero,zero.getBitWidth());  
    Res->GeneralizedJoin(vv);
    // it should be [2,135]
#ifdef EVAL
    dbgs()<< "Result for test 1: " ;
    dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10,false) << "]\n";
#endif
  }

  {
    APInt a(8,   1 , false);  APInt b(8,  10 , false);
    APInt c(8, 120 , false);  APInt d(8, 130 , false);
    APInt e(8, 132 , false);  APInt f(8, 135 , false);
    APInt g(8, 220 , false);  APInt h(8,  50 , false);

    APInt zero(8, 0, false); 
    // Temporary constructors
    AbstractValue * R1 = dyn_cast<AbstractValue>(new StridedWrappedRange(a,b,a.getBitWidth()));
    AbstractValue * R2 = dyn_cast<AbstractValue>(new StridedWrappedRange(c,d,c.getBitWidth()));
    AbstractValue * R3 = dyn_cast<AbstractValue>(new StridedWrappedRange(e,f,e.getBitWidth()));
    AbstractValue * R4 = dyn_cast<AbstractValue>(new StridedWrappedRange(g,h,g.getBitWidth()));
    std::vector<AbstractValue*> vv;
    vv.push_back(R3); vv.push_back(R4); vv.push_back(R2); vv.push_back(R1);
    StridedWrappedRange * Res = new StridedWrappedRange(zero,zero,zero.getBitWidth());  
    Res->GeneralizedJoin(vv);
    // it should be [220,135]
#ifdef EVAL
    dbgs()<< "Result for test 2: " ;
    dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10, false) << "]\n";
#endif
  }

  {
    APInt a(3,   0 , false);  APInt b(3,   1 , false);
    APInt c(3,   7 , false);  APInt d(3,   0 , false);
    APInt e(3,   6 , false);  APInt f(3,   7 , false);
    APInt zero(3, 0, false); 
    // Temporary constructors
    AbstractValue * R1 = dyn_cast<AbstractValue>(new StridedWrappedRange(a,b,a.getBitWidth()));
    AbstractValue * R2 = dyn_cast<AbstractValue>(new StridedWrappedRange(c,d,c.getBitWidth()));
    AbstractValue * R3 = dyn_cast<AbstractValue>(new StridedWrappedRange(e,f,e.getBitWidth()));
    AbstractValue * R4 = dyn_cast<AbstractValue>(new StridedWrappedRange(a,b,a.getBitWidth()));
    std::vector<AbstractValue*> vv;
    // vv.push_back(R3); vv.push_back(R4); vv.push_back(R2); vv.push_back(R1);
    vv.push_back(R1); vv.push_back(R2); vv.push_back(R3); vv.push_back(R4);
    StridedWrappedRange * Res = new StridedWrappedRange(zero,zero,zero.getBitWidth());  
    Res->GeneralizedJoin(vv);
    // it should be [6,1]
#ifdef EVAL
    dbgs()<< "Result for test 3: " ;
    dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10, false) << "]\n";
#endif
  }
}


				

