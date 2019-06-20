// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file  WrappedRange.cpp
///        Wrapped Interval Abstract Domain.
///
/// \todo There are still memory leaks: need to fix.
///////////////////////////////////////////////////////////////////////////////

#include "BaseRange.h"
#include "WrappedRange.h"
#include "StridedWrappedRange.h"

#include <algorithm>

using namespace llvm;
using namespace unimelb;

void test_GeneralizedJoin();

// For debugging
//#define DEBUG_FILTER_SIGMA
//#define DEBUG_EVALUATE_GUARD
//#define DEBUG_WIDENING
//#define DEBUG_REFINE_WITH_JUMPS
//#define DEBUG_MEET
//#define DEBUG_JOIN
//#define DEBUG_OVERFLOW_CHECKS
//#define DEBUG_GENERALIZED_JOIN
//#define DEBUG_MEMBER
//#define DEBUG_MULT
//#define DEBUG_DIVISION
//#define DEBUG_CAST
//#define DEBUG_TRUNCATE
//#define DEBUG_SHIFTS
//#define DEBUG_LOGICALBIT

STATISTIC(NumOfOverflows     ,"Number of overflows");
STATISTIC(NumOfJoins         ,"Number of joins");
STATISTIC(NumOfJoinTies      ,"Number of join ties");

void printComparisonOp(unsigned Pred,raw_ostream &Out){
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

bool WrappedRange::isBot() const { 
  return __isBottom;
}

bool WrappedRange::IsTop() const {  
  return BaseRange::IsTop();
}

void WrappedRange::makeBot(){ 
  __isBottom=true;
  __isTop=false;
}

void WrappedRange::makeTop(){ 
  BaseRange::makeTop();
  __isBottom=false;
}

bool WrappedRange::isIdentical(AbstractValue* V){
  return (BaseRange::isIdentical(V));
}

bool WrappedRange::isEqual(AbstractValue* V){
  WrappedRange *S = this;
  WrappedRange *T = cast<WrappedRange>(V);    
  // This is correct since we have a poset and the anti-symmetric
  // property holds.
  return (S->lessOrEqual(T) && T->lessOrEqual(S));
}

#if 0
/// Choose the greatest of the constants that is smaller than lb and
/// the smallest of the constants that it is bigger than ub.
void widenOneInterval(const APInt &a, const APInt &b, unsigned int width,		      
		      const std::vector<int64_t> &JumpSet,
		      APInt &lb, APInt &ub){
  // Initial values 
  lb= APInt::getSignedMinValue(width);
  ub= APInt::getSignedMaxValue(width);
  bool first_lb=true;
  bool first_ub=true;

  for (unsigned int i=0; i < JumpSet.size(); i++)){ 
    APInt LandMark(width, JumpSet[i]);
    if (Lex_LessOrEqual(LandMark,a)){
      if (first_lb){
	lb = LandMark; 
	first_lb=false;
      }
      else 
	lb =  BaseRange::umax(lb,LandMark);// Lex_max(lb,LandMark); 
    }
    if (Lex_LessOrEqual(b,LandMark)){
      if (first_ub) {
	ub = LandMark; 
	first_ub=false;
      }
      else
	ub = BaseRange::umin(ub,LandMark);// Lex_min(lb,LandMark);
    }
}
  
#ifdef DEBUG_WIDENING
  dbgs() << "Widen interval based on landmarks: " 
	 << "[" << lb << "," << ub << "]\n";
#endif 
}
#else
/////
// Optimized version that speed up the analysis significantly.
// This version takes advantage of the fact that JumpSet is sorted.
/////
void widenOneInterval(const APInt &a, const APInt &b, unsigned int width,		      
		      const std::vector<int64_t> &JumpSet,
		      APInt &lb, APInt &ub){

  // lb_It points to the first element that is not less than lb
  std::vector<int64_t>::const_iterator lb_It= 
    std::lower_bound(JumpSet.begin(), JumpSet.end(), a.getSExtValue(), 
		     Utilities::Lex_LessThan_Comp);

  if (lb_It == JumpSet.end()) // no element is less than a
    lb = a; 
  else{
    if (lb_It == JumpSet.begin()){
      APInt LB_LandMark(width, *(lb_It), false);
      lb = LB_LandMark;
    }
    else{
      APInt LB_LandMark(width, *(lb_It-1), false);
      lb = LB_LandMark;
    }
  }

  // ub_It points to the first element that is greater than ub
  std::vector<int64_t>::const_iterator ub_It= 
    std::upper_bound(JumpSet.begin(), JumpSet.end(), b.getSExtValue(), 
		     Utilities::Lex_LessThan_Comp);

  if (ub_It == JumpSet.end()) // no element is greater than b
    ub = b; 
  else{
    APInt UB_LandMark(width, *ub_It, false);
    ub = UB_LandMark;
  }

#ifdef DEBUG_WIDENING
  dbgs() << "Widen interval based on landmarks: " 
	 << "[" << lb << "," << ub << "]\n";
#endif 
}
#endif  /* end wideningOneInterval */

bool checkOverflowForWideningJump(const APInt &Card){
  // If a or b do not fit into uint64_t or they do not have same width
  // then APInt raises an exception
  uint64_t value = Card.getZExtValue();
  // Max is 2^{w-1}
  uint64_t Max = (APInt::getSignedMaxValue(Card.getBitWidth() -1)).getZExtValue();
    
#ifdef DEBUG_WIDENING
  dbgs() << "\n\tchecking if the widening jump overflows: " 
	 << value << ">?" << Max << "\n";
#endif
  return (value >= Max);
}

/// After trivial cases, we check in what direction we are growing and
/// doubling the size of one the intervals. We also use the constants
/// of the program to make guesses.
void WrappedRange::widening(AbstractValue *PreviousV, 
                            const std::vector<int64_t> &JumpSet){

  if (PreviousV->isBot()) return;
  // rest of trivial cases are handled by the caller (e.g., if any of
  // the two abstract values is top).

  WrappedRange *Old = cast<WrappedRange>(PreviousV->clone());  
  WrappedRange *New = this;

  // if (New->lessOrEqual(Old)) return;

  APInt u = Old->getLB();
  APInt v = Old->getUB();
  APInt x = New->getLB();
  APInt y = New->getUB();

  DEBUG(dbgs() << "\t" << getValue()->getName()  
	       <<  " WIDENING("  << *Old << "," << *this << ")=");
	    
  bool canDoublingInterval=true;
  APInt cardOld  = WCard(u,v);

  // Overflow check   
  if (checkOverflowForWideningJump(cardOld)){
    CounterWideningCannotDoubling++;
#ifdef DEBUG_WIDENING
    dbgs() << "### \n";
#endif
    if (CounterWideningCannotDoubling < 5){ // here some constant value
      canDoublingInterval=false;
    }
    else{
      New->makeTop();
      DEBUG(dbgs() <<  *New << "\n");
      CounterWideningCannotDoubling=0;
      return;
    }
  }

#ifdef DEBUG_WIDENING
  dbgs() <<  "\n ### \n";
  dbgs() << "Size of [" << u << "," << v << "]: " << cardOld.toString(10,false) << "\n";
#endif 
  WrappedRange Merged(*Old);
  Merged.join(New);  
#ifdef DEBUG_WIDENING
  dbgs() << "Upper bound of old and new value: ";
  Merged.printRange(dbgs());
  dbgs() << "\n";
#endif 

  unsigned int width = x.getBitWidth();
  if ( Old->lessOrEqual(New) &&  
      (!Old->WrappedMember(x) && !Old->WrappedMember(y))) {
#ifdef DEBUG_WIDENING
    dbgs() << "Neither of the two extremes stabilize.\n";
#endif 
    if (!canDoublingInterval){
      APInt widen_lb; APInt widen_ub;
      widenOneInterval(Merged.getLB(), Merged.getUB(), width, 
		       JumpSet, widen_lb, widen_ub);
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      WrappedRange tmp(x,y,width); 
      New->join(&tmp);
#ifdef DEBUG_WIDENING
      dbgs() << "We cannot doubling the interval so we use landmarks:\n";
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
    }
    else{
      APInt widen_lb = x;
      APInt widen_ub = x + cardOld + cardOld; 
#ifdef DEBUG_WIDENING
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
      APInt jump_lb; APInt jump_ub;
      widenOneInterval(Merged.getLB(), Merged.getUB(), width, 
	               JumpSet, jump_lb, jump_ub);
      {
	WrappedRange tmp = 
	  mkSmallerInterval(Merged.getLB(), widen_lb, width);
	if (tmp.WrappedMember(jump_lb)) 
	  widen_lb = jump_lb;
      }
      {
	WrappedRange tmp = 
	  mkSmallerInterval(Merged.getUB(), widen_ub, width);
	if (tmp.WrappedMember(jump_ub)) 
	  widen_ub = jump_ub;
      }
#ifdef DEBUG_WIDENING
      dbgs() << "After refinement with landmarks:\n";
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      WrappedRange tmp(x,y,width); 
      New->join(&tmp);
    }
  }
  else if ( (Merged.getLB() == u) && (Merged.getUB() == y)){
#ifdef DEBUG_WIDENING
    dbgs() << "The upper bound does not stabilize but the lower bound does.\n";
#endif 
    if (!canDoublingInterval){
      APInt widen_lb = u; APInt widen_lb__;
      APInt widen_ub;
      widenOneInterval(Merged.getLB(), Merged.getUB(), width, 
	               JumpSet, widen_lb__, widen_ub);
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      WrappedRange tmp(x,y,width); 
      New->join(&tmp);
#ifdef DEBUG_WIDENING
      dbgs() << "We cannot doubling the interval so we use landmarks:\n";
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
    }
    else{
      APInt widen_lb = u;
      APInt widen_ub = u + cardOld + cardOld; 
#ifdef DEBUG_WIDENING
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
      APInt jump_lb__; APInt jump_ub;
      widenOneInterval(Merged.getLB(), Merged.getUB(), width, 
		       JumpSet, jump_lb__, jump_ub);
      {
	WrappedRange tmp = mkSmallerInterval(Merged.getUB(), widen_ub, width);
	if (tmp.WrappedMember(jump_ub)) 
	  widen_ub = jump_ub;
      }
#ifdef DEBUG_WIDENING
      dbgs() << "After refinement with landmarks:\n";
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      WrappedRange tmp(u,y,width); 
      New->join(&tmp);
    }
  }
  else if ( (Merged.getLB() == x) && (Merged.getUB() == v)){
#ifdef DEBUG_WIDENING
    dbgs() << "The lower bound does not stabilize but the upper bound does.\n";
#endif
    if (!canDoublingInterval){
      APInt widen_lb; 
      APInt widen_ub = v; APInt widen_ub__;
      widenOneInterval(Merged.getLB(), Merged.getUB(), width, 
		       JumpSet, widen_lb, widen_ub__);
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      WrappedRange tmp(x,y,width); 
      New->join(&tmp);
#ifdef DEBUG_WIDENING
      dbgs() << "We cannot doubling the interval so we use landmarks:\n";
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
    }
    else{
      APInt widen_lb = u - cardOld - cardOld; 
      APInt widen_ub = v;
#ifdef DEBUG_WIDENING
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif
      APInt jump_lb; APInt jump_ub__;
      widenOneInterval(Merged.getLB(), Merged.getUB(), width, 
	               JumpSet, jump_lb, jump_ub__);
      {
	WrappedRange tmp = mkSmallerInterval(Merged.getLB(), widen_lb, width);
	if (tmp.WrappedMember(jump_lb)) 
	widen_lb = jump_lb;
      }
#ifdef DEBUG_WIDENING
      dbgs() << "After refinement with landmarks:\n";
      dbgs() << "Widen LB= " << widen_lb << "\n";
      dbgs() << "Widen UB= " << widen_ub << "\n";
#endif 
      New->convertWidenBoundsToWrappedRange(widen_lb,widen_ub);
      WrappedRange tmp(x,v,width);
      New->join(&tmp);
    }
  }
  else{
    //assert(false && "Unsupported case");
    // Otherwise, return old interval
    // Watch out here: it should be top!
    New->setLB(Old->getLB());
    New->setUB(Old->getUB());
  }
  
  New->normalizeTop();

#ifdef DEBUG_WIDENING
  dbgs() << "### \n";
#endif

  DEBUG(dbgs()  <<"\t" << getValue()->getName()  << "=" << *this << "\n");
  return;
}

/// Return true if x \in [a,b]. 
bool WrappedRange::WrappedMember(const APInt &e) const{
  if (isBot()) return false;
  if (IsTop()) return true;

  APInt x = getLB();
  APInt y = getUB();

  // This corresponds to the operation e <=_{x} y in page 7 in the
  // paper. e \in [x,y] iff e <=_{x} y (starting from x we encounter e
  // before than y going clockwise) iff e - x <= y - x

#ifdef DEBUG_MEMBER
  dbgs()<< "MEMBERSHIP " << e.toString(10,false) << " in " ;
  print(dbgs());
  dbgs() << "\n";
  dbgs() <<   Lex_LessOrEqual(e - x, y - x) << "\n";
  dbgs() << ( (x.ule(y) && x.ule(e) && e.ule(y)) ||
   	      (x.ugt(y) && (e.ule(x) || y.ule(e)))) << "\n";
#endif /*DEBUG_MEMBER*/

  return Lex_LessOrEqual(e - x, y - x);
}

/// Return true if this is less or equal than V based on the poset
/// ordering.
bool WrappedRange::WrappedlessOrEqual(AbstractValue * V){ 
  
  WrappedRange *S = this;
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
	   (S->isIdentical(T) || 
	    !(S->WrappedMember(c)) || !(S->WrappedMember(d))));	   	    
}


bool WrappedRange::isMoreOrEqualPrecise(AbstractValue * V){ 
  
  WrappedRange *S = this;
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
  
  return ( T->WrappedMember(a) && 
	   T->WrappedMember(b) &&
	   ((a == c && b == d && T->getStride() <= 1) || 
	    !(S->WrappedMember(c)) || !(S->WrappedMember(d))));	      
}


bool WrappedRange::lessOrEqual(AbstractValue * V){ 
  return WrappedlessOrEqual(V);
}

void WrappedRange::print(raw_ostream &Out) const{
    BaseRange::print(Out);
}

void WrappedRange::join(AbstractValue *V){
  WrappedRange * R = cast<WrappedRange>(V);
  if (R->isBot()) 
    return;
  if (isBot()){
    WrappedRangeAssign(R); 
    return;
  }
#if 0
  std::vector<WrappedRangePtr> s1 = 
    WrappedRange::ssplit(R->getLB(), R->getUB(), R->getLB().getBitWidth());
  std::vector<WrappedRangePtr> s2 = 
    WrappedRange::ssplit(getLB(), getUB(), getLB().getBitWidth());
  typedef std::vector<WrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){      
      // FIXME: use GeneralizedJoin to get more precise results.
      this->Binary_WrappedJoin((*I1).get(), (*I2).get());
    }
  }
#else 
  WrappedJoin(R);
#endif 
  normalizeTop();
}

#if 0
//Just a wrapper.
void WrappedRange::Binary_WrappedJoin(WrappedRange *R1, WrappedRange *R2){
  WrappedJoin(R1);
  WrappedJoin(R2);
}
#endif 

void WrappedRange::WrappedJoin(AbstractValue *V){

  WrappedRange *S = this;
  WrappedRange *T = cast<WrappedRange>(V);

  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();
#ifdef DEBUG_JOIN
  dbgs() << " join( " ;
  S->printRange(dbgs()) ; 
  dbgs() << "," ;
  T->printRange(dbgs()) ; 
  dbgs() << ")=" ;
#endif /*DEBUG_JOIN*/
  NumOfJoins++;

  // Containment cases (also cover bottom and top cases)
  if (T->WrappedlessOrEqual(S)) {
#ifdef DEBUG_JOIN
    dbgs() << "containment case\n";
#endif 
  }
  else if (S->WrappedlessOrEqual(T)) {
#ifdef DEBUG_JOIN
    dbgs() << "containment case\n";
#endif 
    WrappedRangeAssign(T);
  }
  // Extra case for top: one cover the other
  else if (T->WrappedMember(a) && T->WrappedMember(b) &&
           S->WrappedMember(c) && S->WrappedMember(d)){
#ifdef DEBUG_JOIN
    dbgs() << "one cover the other case\n";
#endif 
    makeTop();
  }
  // Overlapping cases
  else if (S->WrappedMember(c)){
#ifdef DEBUG_JOIN
    dbgs() << "overlapping case\n";
#endif 
    setLB(a);
    setUB(d);
  }
  else if (T->WrappedMember(a)){
#ifdef DEBUG_JOIN
    dbgs() << "overlapping case\n";
#endif 
    setLB(c);
    setUB(b);
  }
  // Left/Right Leaning cases: non-deterministic cases
  // Here we use lexicographical order to resolve ties
  else if (WCard(b,c) == WCard(d,a)){
    NumOfJoinTies++;
    if (Lex_LessThan(a,c)){
      // avoid crossing NP
      setLB(a);
      setUB(d);
      // crossing NP
      /*
        setLB(c);
        setUB(b);
      */
    }
    else{
      // avoid crossing NP
      setLB(c);
      setUB(b);
      // crossing NP
      /*
        setLB(a);
        setUB(d);
      */
    }
  }
  else if (Lex_LessOrEqual(WCard(b,c), WCard(d,a))){
#ifdef DEBUG_JOIN
    dbgs() << "\nnon-overlapping case (left)\n";
    dbgs() << "Card(b,c)=" << WCard(b,c).toString(10,false) << " "
           << "Card(d,a)=" << WCard(d,a).toString(10,false) << "\n";
#endif 
    setLB(a);
    setUB(d);
  }
  else{
#ifdef DEBUG_JOIN
    dbgs() << "\nnon-overlapping case (right)\n";
    dbgs() << "Card(b,c)=" << WCard(b,c).toString(10,false) << " " 
           << "Card(d,a)=" << WCard(d,a).toString(10,false) << "\n";
#endif 
    setLB(c);
    setUB(b);
  }


//   else if ( Lex_LessOrEqual(WCard(b,c), WCard(d,a)) ||
//             (WCard(b,c) == WCard(d,a) &&  Lex_LessThan(a,c))){
// #ifdef DEBUG_JOIN
//     dbgs() << "\nnon-overlapping case (left)\n";
//     dbgs() << "Card(b,c)="  << WCard(b,c).toString(10,false) << " "
//            << "Card(d,a)=" << WCard(d,a).toString(10,false)  << "\n";
// #endif 
//     setLB(a);
//     setUB(d);
//   }
//   else{
// #ifdef DEBUG_JOIN
//     dbgs() << "\nnon-overlapping case (right)\n";
//     dbgs() << "Card(b,c)="  << WCard(b,c).toString(10,false) << " " 
//            << "Card(d,a)=" << WCard(d,a).toString(10,false)  << "\n";
// #endif 
//     setLB(c);
//     setUB(b);
//   }

  normalizeTop();
  // This is gross but we need to record that this is not bottom
  // anymore.
  if (!S->isBot() || !T->isBot())
    resetBottomFlag();
#ifdef DEBUG_JOIN
  printRange(dbgs()) ; 
  dbgs() << "\n" ;
#endif 
}

// Begin  machinery for generalized join

bool SortWrappedRanges_Compare(WrappedRange *R1, WrappedRange *R2){
  assert(R1);
  assert(R2);
  APInt a = R1->getLB();
  APInt c = R2->getLB();
  return Lex_LessOrEqual(a,c); // a.ule(c);
}

/// Sort a vector of wrapped ranges in order of lexicographical
/// increasing left bound.
void SortWrappedRanges(std::vector<WrappedRange *> & Rs){
#ifdef DEBUG_GENERALIZED_JOIN
  dbgs() << "before sorted: \n";
  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange *R = *I;
    R->printRange(dbgs());
  }
  dbgs() << "\n";
#endif 
  std::sort(Rs.begin(), Rs.end() , SortWrappedRanges_Compare);
#ifdef DEBUG_GENERALIZED_JOIN
  dbgs() << "after sorted: \n";
  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange *R = *I;
    R->printRange(dbgs());
  }
  dbgs() << "\n";
#endif 
}

// Wrapper for join
WrappedRange Extend(const WrappedRange &R1, const  WrappedRange &R2){  
  WrappedRange Res(R1);
  WrappedRange tmp(R2);
  Res.join(&tmp);
  return Res;
}

/// Return the biggest of the two wrapped intervals.
WrappedRange Bigger(const WrappedRange &R1, const WrappedRange &R2){

  if (R1.isBot() && !R2.isBot())
    return WrappedRange(R2);
  if (R2.isBot() && !R1.isBot())
    return WrappedRange(R1);
  if (R2.isBot() && R1.isBot())
    return WrappedRange(R1);

  APInt a = R1.getLB();
  APInt b = R1.getUB();
  APInt c = R2.getLB();
  APInt d = R2.getUB();
  //  if (WrappedRange::WCard(a,b).uge(WrappedRange::WCard(c,d)))
  if (Lex_LessOrEqual(WrappedRange::WCard(c,d),WrappedRange::WCard(a,b)))
    return WrappedRange(R1);
  else 
    return WrappedRange(R2);
}

/// If R1 and R2 overlap then return bottom. Otherwise, return the
/// clockwise distance from the end of the first to the start of the
/// second.
WrappedRange ClockWiseGap(const WrappedRange &R1, const WrappedRange &R2){
  APInt a = R1.getLB();
  APInt b = R1.getUB();
  APInt c = R2.getLB();
  APInt d = R2.getUB();

  WrappedRange gap(b+1,c-1,a.getBitWidth());
  if (R1.isBot() || R2.isBot() || R2.WrappedMember(b) || R1.WrappedMember(c))
    gap.makeBot();
  
  return gap;
}

/// Return the complement of a wrapped interval.
WrappedRange WrappedComplement(const WrappedRange &R){
  WrappedRange C(R);

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


inline WrappedRange * convertAbsValToWrapped(AbstractValue *V){
  return cast<WrappedRange>(V);
}

/// Algorithm Fig 3 from the paper. Finding the pseudo least upper
/// bound of a set of wrapped ranges and assign it to this.
void WrappedRange::
GeneralizedJoin(std::vector<AbstractValue *> Values){

  if (Values.size() < 2) return;

  std::vector<WrappedRange*> Rs;
  std::transform(Values.begin(), Values.end(), 
		 std::back_inserter(Rs), 
		 convertAbsValToWrapped);

  SortWrappedRanges(Rs);  

  WrappedRange f(*this);
  f.makeBot();

  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange R(*(*I));
    if (R.IsTop() || CrossSouthPole(R.getLB(), R.getUB())){      
#ifdef DEBUG_GENERALIZED_JOIN
      dbgs() << R << " crosses the south pole!\n";
      dbgs() << "extend(" << f << "," << R << ")=";
#endif 
      f = Extend(f, R);
#ifdef DEBUG_GENERALIZED_JOIN
      dbgs() << f << "\n";
#endif 
    }
  }

  WrappedRange g(*this);
  g.makeBot();
  for(std::vector<WrappedRange*>::iterator I=Rs.begin(), E=Rs.end() ; I!=E; ++I){
    WrappedRange R(*(*I));
    WrappedRange tmp = ClockWiseGap(f, R);
#ifdef DEBUG_GENERALIZED_JOIN
    dbgs() << "Gap(" << f << "," << R << " = " << tmp  << ")\n";
    dbgs() << "Bigger(" << g << "," << tmp  << ") = ";
#endif 
    g = Bigger(g,tmp);
#ifdef DEBUG_GENERALIZED_JOIN
    dbgs() << g << "\n";
    dbgs() << "Extend(" << f << "," << R << ") = ";
#endif 
    f = Extend(f, R);
#ifdef DEBUG_GENERALIZED_JOIN
    dbgs() << f << "\n";
#endif 
  }

  WrappedRange Tmp = WrappedComplement(Bigger(g,WrappedComplement(f)));
#ifdef DEBUG_GENERALIZED_JOIN
  dbgs() << Tmp << "\n";
#endif 
  this->setLB(Tmp.getLB());
  this->setUB(Tmp.getUB());
}

// End  Machinery for generalized join

void WrappedRange::meet(AbstractValue *V1, AbstractValue *V2){
			  
  WrappedRange * R1 = cast<WrappedRange>(V1);
  WrappedRange * R2 = cast<WrappedRange>(V2);

#if 0
  this->makeBot();
  // **SOUTH POLE SPLIT** 
  std::vector<WrappedRangePtr> s1 = 
    WrappedRange::ssplit(R1->getLB(), R1->getUB(), R1->getLB().getBitWidth());
  std::vector<WrappedRangePtr> s2 = 
    WrappedRange::ssplit(R2->getLB(), R2->getUB(), R2->getLB().getBitWidth());

  typedef std::vector<WrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){      
      // Note that we need to meet each pair of segments and then join
      // the result of all of them.
      WrappedRange tmp = WrappedMeet((*I1).get(),(*I2).get());
      this->WrappedJoin(&tmp);
    }
  }
#else
  this->makeBot();
  WrappedRange tmp = WrappedMeet(R1,R2);
  this->WrappedJoin(&tmp);
#endif 


}


WrappedRange unimelb::
WrappedMeet(WrappedRange *S, WrappedRange *T){

  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();

#ifdef DEBUG_MEET
  dbgs() << "meet(" << *S << "," << *T << ")\n";
#endif 

  APInt lb; APInt ub;
  unsigned int width = a.getBitWidth();

  // Containment cases (also cover bottom and top cases)
  if (S->WrappedlessOrEqual(T)) {
#ifdef DEBUG_MEET
    dbgs() << "Containment case 1\n";
#endif
    lb = S->getLB();
    ub = S->getUB();
  }
  else if (T->WrappedlessOrEqual(S)) {
#ifdef DEBUG_MEET
    dbgs() << "Containment case 2\n";
#endif
    lb = T->getLB();
    ub = T->getUB();
  }
  // If one cover the other the meet is not convex.  We return the one
  //  with smallest cardinality
  else if (T->WrappedMember(a) && T->WrappedMember(b) &&
	   S->WrappedMember(c) && S->WrappedMember(d)){
#ifdef DEBUG_MEET
    dbgs() << "One cover the other\n";
#endif
    //   if (Lex_LessOrEqual(WCard(a,b), WCard(c,b))){
    if ( Lex_LessThan(WrappedRange::WCard(a,b), 
		      WrappedRange::WCard(c,d)) || 
	 ( WrappedRange::WCard(a,b) == WrappedRange::WCard(c,d) && 
	   Lex_LessOrEqual(a,c))){
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
#ifdef DEBUG_MEET
    dbgs() << "Overlapping 1\n";
#endif
    lb = c;
    ub = b;
  }
  else if (T->WrappedMember(a)){
#ifdef DEBUG_MEET
    dbgs() << "Overlapping 2\n";
#endif
    lb = a;
    ub = d;
  }
  else{
#ifdef DEBUG_MEET
    dbgs() << "Disjoint case\n";
#endif
    // Otherwise, bottom
    // a and b to put something initilized.
    WrappedRange Meet(a,b,width);   
    Meet.makeBot();
    return Meet;
  }
  
  WrappedRange Meet(lb,ub,width);   
  Meet.normalizeTop();
  #ifdef DEBUG_MEET
    dbgs() << "Meet Result:" << Meet << "\n";
#endif
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
inline bool comparisonSle_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <=_s " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().sle(I2->getUB());
}

/// [a,b] < [c,d] if a < d.
inline bool comparisonSlt_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <_s " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().slt(I2->getUB());
}

/// [a,b] <= [c,d] if a <= d.
inline bool comparisonUle_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <=_u " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().ule(I2->getUB());
}

/// [a,b] < [c,d]  if a < d.
inline bool comparisonUlt_SameHemisphere(WrappedRange *I1, WrappedRange *I2){
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\n\t";
  I1->printRange(dbgs());  
  dbgs() << " <_u " ;
  I2->printRange(dbgs());  
  dbgs() << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return I1->getLB().ult(I2->getUB());
}

bool comparisonSignedLessThan(WrappedRange *I1,WrappedRange *I2, bool IsStrict){
  // If IsStrict=true then <= else <
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\t"; 
  I1->printRange(dbgs());
  if (IsStrict) dbgs() << " <_s "; else dbgs() << " <=_s ";    
  I2->printRange(dbgs());
#endif /*DEBUG_EVALUATE_GUARD*/
  // **NORTH POLE SPLIT** and do normal test for all possible
  // pairs. If one is true then return true.
  std::vector<WrappedRangePtr> s1 = 
    WrappedRange::nsplit(I1->getLB(), I1->getUB(), 
			 I1->getLB().getBitWidth());
  std::vector<WrappedRangePtr> s2 = 
    WrappedRange::nsplit(I2->getLB(), I2->getUB(), 
			 I2->getLB().getBitWidth());
  bool tmp=false;
  typedef std::vector<WrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      if (IsStrict)
	tmp |= comparisonSlt_SameHemisphere((*I1).get(), (*I2).get());
      else
	tmp |= comparisonSle_SameHemisphere((*I1).get(), (*I2).get());
      if (tmp) {
#ifdef DEBUG_EVALUATE_GUARD
	dbgs() <<": true\n";
#endif /*DEBUG_EVALUATE_GUARD*/
	// we dont' bother check all of them if one is already true
	return true; 
      }
    }    
  }
#ifdef DEBUG_EVALUATE_GUARD
  if (tmp) dbgs() <<": true\n";
  else dbgs() <<": false\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return tmp;
}

 bool comparisonUnsignedLessThan(WrappedRange *I1, WrappedRange *I2, 
				 bool IsStrict){
  // If IsStrict=true then <= else <
#ifdef DEBUG_EVALUATE_GUARD
  dbgs() << "\t" << *I1 ; 
  if (IsStrict) dbgs() << " <_u "; else dbgs() << " <=_u ";
  dbgs() << *I2 << "\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  // **SOUTH POLE SPLIT** and do normal test for all possible
  // pairs. If one is true then return true.
  std::vector<WrappedRangePtr> s1 = 
    WrappedRange::ssplit(I1->getLB(), I1->getUB(), 
			 I1->getLB().getBitWidth());
  std::vector<WrappedRangePtr> s2 = 
    WrappedRange::ssplit(I2->getLB(), I2->getUB(), 
			 I2->getLB().getBitWidth());

  bool tmp=false;
  typedef std::vector<WrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      if (IsStrict)
	tmp |= comparisonUlt_SameHemisphere((*I1).get(), (*I2).get());
      else
	tmp |= comparisonUle_SameHemisphere((*I1).get(), (*I2).get());
      if (tmp){
#ifdef DEBUG_EVALUATE_GUARD
	dbgs() <<": true\n";
#endif /*DEBUG_EVALUATE_GUARD*/
	// we dont' bother check all of them if one is already true
	return true; 
      }
    }    
  }
#ifdef DEBUG_EVALUATE_GUARD
  if (tmp) dbgs() <<": true\n";
  else dbgs() <<": false\n";
#endif /*DEBUG_EVALUATE_GUARD*/
  return tmp;
}

bool WrappedRange::comparisonSle(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonSignedLessThan(I1,I2,false);
}

bool WrappedRange::comparisonSlt(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonSignedLessThan(I1,I2,true);
}

bool WrappedRange::comparisonUle(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonUnsignedLessThan(I1,I2,false);
}

bool WrappedRange::comparisonUlt(AbstractValue *V){
  WrappedRange *I1 = this;
  WrappedRange *I2 = cast<WrappedRange>(V);  
  return comparisonUnsignedLessThan(I1,I2,true);

}

// Filter methods: they can refine an interval by using information
// from other variables that appear in the guards.

std::vector<std::pair<WrappedRangePtr,WrappedRangePtr> > 
keepOnlyFeasibleRanges(unsigned Pred, 
		       WrappedRange *V1, WrappedRange *V2){

  std::vector<std::pair<WrappedRangePtr,WrappedRangePtr> > res;
  std::vector<WrappedRangePtr> s1,s2;

  if (BaseRange::IsSignedCompInst(Pred)){
    // **NORTH POLE SPLIT**
    s1 = WrappedRange::nsplit(V1->getLB(), V1->getUB(), 
			      V1->getLB().getBitWidth());
    s2 = WrappedRange::nsplit(V2->getLB(), V2->getUB(), 
			      V2->getLB().getBitWidth());
  }
  else{
    // **SOUTH POLE SPLIT**
    s1 = WrappedRange::ssplit(V1->getLB(), V1->getUB(), 
			      V1->getLB().getBitWidth());
    s2 = WrappedRange::ssplit(V2->getLB(), V2->getUB(), 
			      V2->getLB().getBitWidth());
  }
      
  typedef std::vector<WrappedRangePtr>::iterator It;
  for (It I1=s1.begin(), E1=s1.end(); I1!=E1; ++I1){
    for (It I2=s2.begin(), E2=s2.end(); I2!=E2; ++I2){
      switch(Pred){
      case ICmpInst::ICMP_EQ:
      case ICmpInst::ICMP_NE:
	// FIMXE: no check??
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
	/////
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
void WrappedRange::
filterSigma(unsigned Pred, AbstractValue *V1, AbstractValue *V2){

  WrappedRange *Var1   = cast<WrappedRange>(V1);
  WrappedRange *Var2   = cast<WrappedRange>(V2);
  WrappedRange Tmp(*this);

#ifdef DEBUG_FILTER_SIGMA
  dbgs() << "Before splitting at north/south poles: " ;
  Var1->printRange(dbgs()); 
  printComparisonOp(Pred,dbgs());    
  Var2->printRange(dbgs()); 
  dbgs() << "\n";      
#endif /*DEBUG_FILTER_SIGMA*/
  typedef std::pair<WrappedRangePtr,WrappedRangePtr> WrappedPtrPair; 
  std::vector<WrappedPtrPair> s = keepOnlyFeasibleRanges(Pred,Var1,Var2);
  // During narrowing (this) has a value from the fixpoint computation
  // which we want to (hopefully) improve. This is why we make this bottom. 
  this->makeBot();

  for (std::vector<WrappedPtrPair>::iterator 
	 I = s.begin(), E = s.end(); I!=E; ++I){
    WrappedRange * WI1 = I->first.get();
    WrappedRange * WI2 = I->second.get();
#ifdef DEBUG_FILTER_SIGMA
    dbgs() << "\tAfter cutting the original intervals: "
           << " (" ;
    WI1->printRange(dbgs()); 
    printComparisonOp(Pred,dbgs());
    WI2->printRange(dbgs()); 
    dbgs() << ")\n";      
#endif /*DEBUG_FILTER_SIGMA*/
    // Note that we have only two cases since I1 is the default
    // value for the sigma node unless it can be improved using I2.
    //
    // We have two specialized methods if I2 is also a constant
    // interval or not.
    if (WI2->IsConstantRange()){
      Tmp.filterSigma_VarAndConst(Pred, WI1, WI2);
#ifdef DEBUG_FILTER_SIGMA
      dbgs() << "\tCase 1: variable and constant.\n";
      dbgs() << "\tREFINED INTERVAL: ";
      Tmp.printRange(dbgs());
      dbgs() << "\n";
#endif /*DEBUG_FILTER_SIGMA*/
      this->WrappedJoin(&Tmp);
    }
    else{
      Tmp.filterSigma_TwoVars(Pred, WI1, WI2);
#ifdef DEBUG_FILTER_SIGMA
      dbgs() << "\tCase 2: two variables.\n";
      dbgs() << "\tREFINED INTERVAL: ";
      Tmp.printRange(dbgs());
      dbgs() << "\n";
#endif /*DEBUG_FILTER_SIGMA*/
      this->WrappedJoin(&Tmp);
    }
  } //end for  

  // IMPORTANT: if after cutting intervals at poles, refine them (if
  // possible) and join finally them the result is bottom then it
  // means that could not improve so we should assign Var1 to this
  if (this->isBot())
    this->WrappedRangeAssign(Var1);
  #ifdef DEBUG_FILTER_SIGMA
    dbgs() << "\n RETURNING SIGMA\n";
  #endif
  this->normalizeTop();    
  return;
}


/// Special case when one is variable and the other a constant in the
/// branch condition.
/// Pre: V is not top because it has been split before at the poles
void WrappedRange::
filterSigma_VarAndConst(unsigned Pred, WrappedRange *V, WrappedRange *N){
  // Assumption: V is the range we would like to improve using   
  // information from Pred and N
  WrappedRange *LHS = this;
  // This is also gross but we need to turn off the bottom flag. Of
  // course, if the meet operation returns bottom then the
  // bottom flag will turn on again.
  LHS->resetBottomFlag();

  // V can be a constant interval after we split at the poles!
  // assert(!V->IsConstantRange() && N->IsConstantRange());
  
  #ifdef DEBUG_FILTER_SIGMA
  dbgs() << "Var and Const:1";
  V->printRange(dbgs());
  dbgs() << ", 2:";
  N->printRange(dbgs());
  dbgs() << "\n";
  #endif
  
  switch (Pred){
  case ICmpInst::ICMP_EQ:
    { /* if v == n then [n,n] */       
      LHS->setLB(N->getLB());
      LHS->setUB(N->getUB());    
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
      }
      return;
    }
  case ICmpInst::ICMP_ULE:
  case ICmpInst::ICMP_SLE:
    { /* if v <= n then rng(v) /\ [-oo,n] */      
      // prepare the range [-oo,n]
      // we use signed or unsigned min depending on the instruction
      WrappedRange TmpRng(*N);      
      TmpRng.setLB(getMinValue(Pred)); 	      
      WrappedRange meet = WrappedMeet(V,&TmpRng);
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
      WrappedRange TmpRng(*N);      
      TmpRng.setLB(getMinValue(Pred));      
      // if (N->getLB() == APInt::getMinValue(LHS->getWidth())) // to avoid overflow
      // 	TmpRng->setUB(N->getLB());        
      // else
      TmpRng.setUB(N->getLB() - 1);   	
      WrappedRange meet = WrappedMeet(V,&TmpRng);
      
      #ifdef DEBUG_FILTER_SIGMA
      dbgs() << "\nMeetValSLT:";
      TmpRng.printRange(dbgs());
      meet.printRange(dbgs());
      dbgs() << "\n";
      #endif
      
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
      WrappedRange TmpRng(*N);
      TmpRng.setUB(getMaxValue(Pred));
      // if (N->getUB() == APInt::getMaxValue(LHS->getWidth())) // to avoid overflow
      // 	TmpRng->setLB(N->getUB());       
      // else
      TmpRng.setLB(N->getUB() + 1);       
      WrappedRange meet = WrappedMeet(V,&TmpRng);
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
      WrappedRange TmpRng(*N);
      TmpRng.setLB(N->getUB()); 
      TmpRng.setUB(getMaxValue(Pred)); 
      WrappedRange meet = WrappedMeet(V,&TmpRng);
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
void WrappedRange::
  filterSigma_TwoVars(unsigned Pred, WrappedRange *I1, WrappedRange *I2){
		      
  WrappedRange *LHS  = this;  
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
    return;
  }

  ///// KEY OPERATION and difference wrt to Range class.  FIXME: we
  ///// should have this operation like a template for reusing
  WrappedRange meet =  WrappedMeet(I1,I2);

#ifdef DEBUG_FILTER_SIGMA
  dbgs() << "\tmeet of two variables involved in the comparison: " 
	 <<  meet << "\n";
#endif 

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
bool IsWrappedOverflow_AddSub(const APInt &a, const APInt &b, const APInt &c, const APInt &d){
  // a,b,c,d are unsigned 
  //
  // If the four APInt's do not have the same width then APInt raises
  // an exception.
  unsigned width = a.getBitWidth();
  APInt tmp1  = WrappedRange::WCard(a,b);  
  APInt tmp2  = WrappedRange::WCard(c,d);  
  // If tmp1 or tmp2 do not fit into uint64_t then APInt raises an
  // exception.
  uint64_t n1  =  tmp1.getZExtValue();
  uint64_t n2  =  tmp2.getZExtValue();
  uint64_t Max = (APInt::getMaxValue(width)).getZExtValue() + 1;
#ifdef DEBUG_OVERFLOW_CHECKS
  dbgs() << "\nOverflow test: " << n1 << "+" << n2 << " >= " << Max << "\n";
#endif
  return ((n1 + n2) > Max);
}


/// Return true iff overflow during left shift.
bool IsWrappedOverflow_Shl(WrappedRange * Op, const APInt &shift){
  APInt a = Op->getLB();
  APInt b = Op->getUB();
  APInt tmp  = WrappedRange::WCard(a,b);
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
std::vector<WrappedRangePtr> 
WrappedRange::nsplit(const APInt &x, const APInt &y, unsigned width){

  // Temporary wrapped interval for north pole
  APInt NP_lb = APInt::getSignedMaxValue(width); // 0111...1
  APInt NP_ub = APInt::getSignedMinValue(width); // 1000...0
  WrappedRange NP(NP_lb,NP_ub,width);

  // Temporary wrapped interval 
  WrappedRangePtr s(new WrappedRange(x,y,width));

  std::vector<WrappedRangePtr> res;
  if (!(NP.WrappedlessOrEqual(s.get()))){
    ////
    // No need of split
    ////
    res.push_back(s);
    return res;
  }
  else{
    // Split into two wrapped intervals
    WrappedRangePtr s1(new WrappedRange(x,NP_lb,width)); // [x,  0111...1]
    WrappedRangePtr s2(new WrappedRange(NP_ub,y,width)); // [1000....0, y]
    res.push_back(s1);
    res.push_back(s2);
    return res;  
  }
}

/// Cut only at south pole
std::vector<WrappedRangePtr> 
WrappedRange::ssplit(const APInt &x, const APInt &y, unsigned width){
  // Temporary wrapped interval for south pole
  APInt SP_lb = APInt::getMaxValue(width); // 111...1
  APInt SP_ub(width, 0, false);
  //                    ^^^^^ unsigned
  WrappedRange SP(SP_lb,SP_ub,width);
  // Temporary wrapped interval 
  WrappedRangePtr s(new WrappedRange(x,y,width));

  std::vector<WrappedRangePtr> res;
  if (!(SP.WrappedlessOrEqual(s.get()))){
    ////
    // No need of split
    ////
    res.push_back(s);
    return res;
  }
  else{
    // Split into two wrapped intervals
    WrappedRangePtr s1(new WrappedRange(x,SP_lb,width)); // [x, 111....1]
    WrappedRangePtr s2(new WrappedRange(SP_ub,y,width)); // [000...0,  y] 
    res.push_back(s1);
    res.push_back(s2);
    return res;  
  }
}

/// Cut both at north and south poles
std::vector<WrappedRangePtr> psplit(const APInt &x, const APInt &y, unsigned width){

  std::vector<WrappedRangePtr> res;  
  std::vector<WrappedRangePtr> s1 = WrappedRange::nsplit(x,y,width);

  for (std::vector<WrappedRangePtr>::iterator I = s1.begin(),
	 E=s1.end() ; I!=E ; ++I){
    WrappedRange *r = (*I).get();
    std::vector<WrappedRangePtr> s2  = 
      WrappedRange::ssplit(r->getLB(),r->getUB(),r->getLB().getBitWidth());
    // append all elements of s2 into res
    res.insert(res.end(),s2.begin(),s2.end());
  }
  return res;
}

std::vector<WrappedRangePtr>  purgeZero(WrappedRangePtr RPtr){
  std::vector<WrappedRangePtr> purgedZeroIntervals; 
  WrappedRange * R = RPtr.get();

  assert(!(R->getLB() == 0  && R->getUB() == 0) && "Interval cannot be [0,0]");

  unsigned width = R->getLB().getBitWidth();
  // Temporary wrapped interval for zero
  APInt Zero_lb(width, 0, false);          // 000...0 
  APInt Zero_ub(width, 0, false);          // 000...0 
  WrappedRange Zero(Zero_lb,Zero_ub,width);

  if (Zero.lessOrEqual(R)){
    if (R->getLB() == 0){
      if (R->getUB() != 0){
	// Does not cross the south pole
	WrappedRangePtr s(new WrappedRange(R->getLB()+1,R->getUB(),width)); 
	purgedZeroIntervals.push_back(s);      
      }
    }
    else{
      if (R->getUB() == 0){
	// If interval is e.g., [1000,0000] then we keep one interval
	APInt minusOne = APInt::getMaxValue(width); // 111...1
	WrappedRangePtr s(new WrappedRange(R->getLB(),minusOne  ,width)); // [x, 111....1]
	purgedZeroIntervals.push_back(s);
      }
      else{
	// Cross the south pole: split into two intervals
	APInt plusOne(width, 1, false);              // 000...1 
	APInt minusOne = APInt::getMaxValue(width); // 111...1
	WrappedRangePtr s1(new WrappedRange(R->getLB(),minusOne  ,width)); // [x, 111....1]
	WrappedRangePtr s2(new WrappedRange(plusOne   ,R->getUB(),width));  // [000...1,  y] 
	purgedZeroIntervals.push_back(s1);
	purgedZeroIntervals.push_back(s2);
      }
    }
  }
  else{  
    // No need of split
    WrappedRangePtr s(new WrappedRange(*R));
    purgedZeroIntervals.push_back(s);
  }

  return purgedZeroIntervals;
}

std::vector<WrappedRangePtr>  
purgeZero(const std::vector<WrappedRangePtr> &Vs){
  std::vector<WrappedRangePtr> res;
  for (unsigned int i=0; i<Vs.size(); i++){
    std::vector<WrappedRangePtr> purgedZeroIntervals = purgeZero(Vs[i]);
    res.insert(res.end(), 
	       purgedZeroIntervals.begin(), 
	       purgedZeroIntervals.end());
  }
  return res;
}
////
// End machinery for arithmetic and bitwise operations
////

WrappedRange UnsignedWrappedMult(const WrappedRange *Op1, 
				 const WrappedRange *Op2){
				   
  WrappedRange Res(*Op1);

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
    Res.setLB(lb);
    Res.setUB(ub);
    return Res;  
  }
}


WrappedRange SignedWrappedMult(const WrappedRange *Op1, 
			       const WrappedRange *Op2){
		       
  WrappedRange Res(*Op1);

  APInt a = Op1->getLB();
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();
  APInt d = Op2->getUB();

  bool IsZero_a = IsMSBZero(a);
  bool IsZero_b = IsMSBZero(b);
  bool IsZero_c = IsMSBZero(c);
  bool IsZero_d = IsMSBZero(d);

  // [2,5]   * [10,20]   = [20,100]
  if (IsZero_a && IsZero_b && IsZero_c && IsZero_d){
    bool Overflow1, Overflow2;
    APInt lb = a.smul_ov(c,Overflow1);
    APInt ub = b.smul_ov(d,Overflow2);
    if (!Overflow1 && !Overflow2){
      Res.setLB(lb);
      Res.setUB(ub);
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
      return Res;
    }
  }
  else 
    llvm_unreachable("Unsupported case!");

  NumOfOverflows++;  
  Res.makeTop();

  return Res;
}


void WrappedRange::WrappedMultiplication(WrappedRange *LHS, 
					  const WrappedRange *Op1, 
					  const WrappedRange *Op2){
  // Trivial case
  if (Op1->IsZeroRange() || Op2->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    return;
  }
  
  // General case: south pole and north pole cuts, meet the signed and
  // unsigned operation for each element of the Cartesian product and
  // then lubbing them
  std::vector<WrappedRangePtr> s1 = 
    psplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth());
  std::vector<WrappedRangePtr> s2 = 
    psplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth());

  LHS->makeBot();  
  typedef std::vector<WrappedRangePtr>::iterator It;
  for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      WrappedRange Tmp1 = UnsignedWrappedMult((*I1).get(),(*I2).get());
      WrappedRange Tmp2 = SignedWrappedMult((*I1).get(),(*I2).get());
#ifdef DEBUG_MULT
      dbgs() << "Op1=" << *((*I1).get()) << " Op2=" << *((*I2).get()) << "\n";
      dbgs() << "Unsigned version    : " << Tmp1 << "\n";
      dbgs() << "Signed version      : " << Tmp2 << "\n";
#endif 
      WrappedRange tmp = WrappedMeet(&Tmp1,&Tmp2);
#ifdef DEBUG_MULT
      dbgs() << "The best of the two : " << tmp << "\n";
#endif 
      // TODO: better call to GeneralizedJoin with all Tmps's
      LHS->join(&tmp);
#ifdef DEBUG_MULT
      dbgs() << "Final multiplication so far : " << *LHS << "\n";
#endif 
    }
  }
#ifdef DEBUG_MULT
  dbgs() << "-----------------------------------\n";
#endif 
}


// Pre: Divisor does not contain the interval [0,0] and does not
// straddle the poles.
WrappedRange WrappedUnsignedDivision(WrappedRange const *Dividend, 
				     WrappedRange const *Divisor){

  WrappedRange Res(*Dividend);
  APInt a = Dividend->getLB();
  APInt b = Dividend->getUB();
  APInt c = Divisor->getLB();
  APInt d = Divisor->getUB();
  
  Res.setLB(a.udiv(d));
  Res.setUB(b.udiv(c));
  return Res;
}

// Pre: Divisor does not contain the interval [0,0] and does not
// straddle the poles.
WrappedRange WrappedSignedDivision(WrappedRange const *Dividend, 
				   WrappedRange const *Divisor, 
				   bool & IsOverflow){

  IsOverflow = false;

  WrappedRange Res(*Dividend);
  APInt a = Dividend->getLB();
  APInt b = Dividend->getUB();
  APInt c = Divisor->getLB();
  APInt d = Divisor->getUB();

#ifdef DEBUG_DIVISION  
  dbgs() << "After removing [0,0] and cutting at poles: ";
  dbgs() << "[" << a << "," << b << "] /_s ";
  dbgs() << "[" << c << "," << d << "]\n";
#endif 

  bool IsZero_a = IsMSBZero(a);
  bool IsZero_c = IsMSBZero(c);

  if (IsZero_a && IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(a.sdiv_ov(d,IsOverflow1));
    Res.setUB(b.sdiv_ov(c,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
#ifdef DEBUG_DIVISION  
    dbgs() << "\tMSB(a)=MSB(c)=0\n\t";
    dbgs() << Res << "\n";
#endif 
    return Res;
  }
  else if (!IsZero_a && !IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(b.sdiv_ov(c,IsOverflow1));
    Res.setUB(a.sdiv_ov(d,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
#ifdef DEBUG_DIVISION  
    dbgs() << "\tMSB(a)=MSB(c)=1\n\t";
    dbgs() << Res << "\n";
#endif 
    return Res;    
  }
  else if (IsZero_a && !IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(b.sdiv_ov(d,IsOverflow1));
    Res.setUB(a.sdiv_ov(c,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
#ifdef DEBUG_DIVISION  
    dbgs() << "\tMSB(a)=0, MSB(c)=1\n\t";
    dbgs() << Res << "\n";
#endif 
    return Res;    
  }
  else if (!IsZero_a && IsZero_c){
    bool IsOverflow1, IsOverflow2;
    Res.setLB(a.sdiv_ov(c,IsOverflow1));
    Res.setUB(b.sdiv_ov(d,IsOverflow2));
    IsOverflow = IsOverflow1 || IsOverflow2;
#ifdef DEBUG_DIVISION  
    dbgs() << "\tMSB(a)=1, MSB(c)=0\n\t";
    dbgs() << Res << "\n";
#endif 
    return Res;    
  }

  llvm_unreachable("This should be unreachable");
}

void WrappedRange::WrappedDivision(WrappedRange *LHS, 
				   const WrappedRange *Dividend, 
				   const WrappedRange *Divisor, 
				   bool IsSignedDiv){

  // Trivial cases
  if (Dividend->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    return;
  }
  if (Divisor->IsZeroRange()){
    LHS->makeBot();
    return;
  }

#ifdef DEBUG_DIVISION  
  dbgs() << "\nBefore removing [0,0] and cutting at poles: \n\t";
  dbgs() << *Dividend << " /_s " << *Divisor << "\n";
#endif 
  
  if (IsSignedDiv){
    // General case: south pole and north pole cuts and compute signed
    // operation for each element of the Cartesian product and then
    // lubbing them. Note that we make sure that [0,0] is removed from
    // the divisor.
    std::vector<WrappedRangePtr> s1 = 
      psplit(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth());
    std::vector<WrappedRangePtr> s2 = 
      purgeZero(psplit(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");

    typedef std::vector<WrappedRangePtr>::iterator It;
    LHS->makeBot();  
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
   	bool IsOverflow;
	WrappedRange Tmp = WrappedSignedDivision((*I1).get(),(*I2).get(),
						 IsOverflow);
  	if (IsOverflow){
  	  NumOfOverflows++;
  	  LHS->makeTop();
  	  break;
  	}
  	LHS->join(&Tmp);
      }
    }
  }
  else{
    // General case: south pole cut and compute unsigned operation for
    // each element of the Cartesian product and then lubbing
    // them. Note that we make sure that [0,0] is removed from the
    // divisor.
    std::vector<WrappedRangePtr> s1 = 
      ssplit(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth());
    std::vector<WrappedRangePtr> s2 = 
      purgeZero(ssplit(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");
    LHS->makeBot();  
    typedef std::vector<WrappedRangePtr>::iterator It;
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	WrappedRange Tmp = WrappedUnsignedDivision((*I1).get(),(*I2).get());
	LHS->join(&Tmp);
      }
    }
  }
}


void WrappedRange::
  WrappedRem(WrappedRange *LHS, 
	     const WrappedRange *Dividend,  const WrappedRange *Divisor, 
	     bool IsSignedRem){ 

  // Trivial cases
  if (Dividend->IsZeroRange()){
    LHS->setLB((uint64_t) 0);
    LHS->setUB((uint64_t) 0);
    return;
  }
  if (Divisor->IsZeroRange()){
    LHS->makeBot();
    return;
  }
  if (IsSignedRem){
    // General case: south pole cut and compute unsigned operation for
    // each element of the Cartesian product and then lubbing
    // them. Note that we make sure that [0,0] is removed from the
    // divisor.
    std::vector<WrappedRangePtr> s1 = 
      ssplit(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth());

    std::vector<WrappedRangePtr> s2 = 
      purgeZero(ssplit(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");
    LHS->makeBot();  
    typedef std::vector<WrappedRangePtr>::iterator It;
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	APInt a = (*I1).get()->getLB();
	APInt b = (*I1).get()->getUB();
	APInt c = (*I2).get()->getLB();
	APInt d = (*I2).get()->getUB();

	bool IsZero_a = IsMSBZero(a);
	bool IsZero_c = IsMSBZero(c);

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

	WrappedRange tmp(lb,ub,width);	 
	LHS->join(&tmp);
      }
    }
  }
  else{
    // General case: south pole cut and compute unsigned operation for
    // each element of the Cartesian product and then lubbing
    // them. Note that we make sure that [0,0] is removed from the
    // divisor.
    std::vector<WrappedRangePtr> s1 = 
      ssplit(Dividend->getLB(), Dividend->getUB(), 
	     Dividend->getLB().getBitWidth());
    std::vector<WrappedRangePtr> s2 = 
      purgeZero(ssplit(Divisor->getLB(), Divisor->getUB(), 
		       Divisor->getLB().getBitWidth()));
    assert(!s2.empty() && "Sanity check: empty means interval [0,0]");
    LHS->makeBot();  
    typedef std::vector<WrappedRangePtr>::iterator It;
    for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
      for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
	// This is a special case that can improve precision. It can
	// be used also for the signed case. This is described in our
	// journal version:
	// WrappedRange Div = WrappedUnsignedDivision((*I1).get(),(*I2).get());
	// if (WCard(Div.getLB(), Div.getUB()) == 1){
	//   WrappedRange tmp1(*(*I2).get());
	//   WrappedRange tmp2(*(*I2).get());
	//   WrappedMinus(&tmp1,(*I1).get(),&Div);
	//   WrappedMultiplication(&tmp2,&tmp1,(*I2).get());
	//   LHS->join(&tmp2);
	// }
	// else{
	APInt d  = (*I2).get()->getUB();
	APInt lb = APInt(width, 0, false); 
	APInt ub = d - 1;
 	unsigned width = d.getBitWidth();
	WrappedRange tmp(lb,ub,width);	 
	LHS->join(&tmp);
        //}
      }
    }
  }
}

void WrappedRange::
  WrappedPlus(WrappedRange *LHS,
	      const WrappedRange *Op1, const WrappedRange *Op2){
  
  //  [a,b] + [c,d] = [a+c,b+d] if no overflow
  //  top                       otherwise
  if (IsWrappedOverflow_AddSub(Op1->getLB(),Op1->getUB(),
			       Op2->getLB(),Op2->getUB())){
    NumOfOverflows++;
    LHS->makeTop();
    return;
  }
  
  // Addition in APInt performs modular arithmetic
  LHS->setLB(Op1->getLB() + Op2->getLB());
  LHS->setUB(Op1->getUB() + Op2->getUB());
}

void WrappedRange::
  WrappedMinus(WrappedRange *LHS,
	       const WrappedRange *Op1, const WrappedRange *Op2){
		  
    //  [a,b] - [c,d] = [a-d,b-c] if no overflow
    //  top                       otherwise
    if (IsWrappedOverflow_AddSub(Op1->getLB(),Op1->getUB(),
				 Op2->getLB(),Op2->getUB())){
      NumOfOverflows++;
      LHS->makeTop();
      return;
    }
    
    /// minus in APInt performs modular arithmetic
    LHS->setLB(Op1->getLB() - Op2->getUB());
    LHS->setUB(Op1->getUB() - Op2->getLB());
}      


/// Perform the transfer function for binary arithmetic operations.
AbstractValue* WrappedRange::
visitArithBinaryOp(AbstractValue *V1,AbstractValue *V2,
		   unsigned OpCode, const char *OpCodeName){

  // test_GeneralizedJoin();
  
  WrappedRange *Op1 = cast<WrappedRange>(V1);
  WrappedRange *Op2 = cast<WrappedRange>(V2);
  WrappedRange *LHS = new WrappedRange(*this);
        
  DEBUG(dbgs() << "\t [RESULT] ");
  DEBUG(Op1->printRange(dbgs()));
  DEBUG(dbgs() << " " << OpCodeName << " ");
  DEBUG(Op2->printRange(dbgs()));
  DEBUG(dbgs() << " = ");

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
    dbgs() << OpCodeName << "\n";
    llvm_unreachable("Arithmetic operation not implemented");
  } // end switch

 END:
  LHS->normalizeTop();
  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");              
  return LHS;
}

// Pre: Operand is not bottom
// LHS is an in/out argument
void Truncate(WrappedRange *&LHS, WrappedRange *Operand, unsigned k){

  APInt a= Operand->getLB();
  APInt b= Operand->getUB();
  assert(a.getBitWidth() == b.getBitWidth());
  assert(k < a.getBitWidth());

  if ( (a.ashr(k) == b.ashr(k)) && 
       Lex_LessOrEqual(a.trunc(k),b.trunc(k))){
    LHS->setLB(a.trunc(k)); 	  
    LHS->setUB(b.trunc(k)); 
  }
  // APInt will wraparound if +1 overflow so == is modular arithmetic
  else if ( (a.ashr(k)+1 == b.ashr(k)) &&  
	    (!Lex_LessOrEqual(a.trunc(k),b.trunc(k)))){
    LHS->setLB(a.trunc(k)); 	  
    LHS->setUB(b.trunc(k)); 
  }
  else{
    // Otherwise, top
    NumOfOverflows++;
    LHS->makeTop();
  }
#ifdef DEBUG_TRUNCATE
  dbgs() << "trunc([" << a << "," << b << "]) = " << *LHS << "\n";
#endif 
}
 
/// Perform the transfer function for casting operations.
AbstractValue* WrappedRange::
visitCast(Instruction &I, 
	  AbstractValue * V, TBool *TB, bool){

  // Very special case: convert TBool to WrappedRange
  WrappedRange *RHS = NULL;
  if (!V){
    // Special case if the source is a Boolean Flag    
    assert(TB && "ERROR: visitCat assumes that TB != NULL");
    RHS = new WrappedRange(I.getOperand(0), TB);
  }
  else{
    // Common case
    RHS = cast<WrappedRange>(V);    
    assert(!TB && "ERROR: some inconsistency found in visitCast");
  }
  WrappedRange *LHS = new WrappedRange(*this);

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
	std::vector<WrappedRangePtr> s = 
	  ssplit(RHS->getLB(), RHS->getUB(), RHS->getLB().getBitWidth());
	WrappedRange Tmp(*LHS);
	LHS->makeBot();  
	for (std::vector<WrappedRangePtr>::iterator 
	       I=s.begin(), E=s.end(); I!=E; ++I){
	  APInt a = (*I).get()->getLB();
	  APInt b = (*I).get()->getUB();
	  Tmp.setLB(a.zext(k));
	  Tmp.setUB(b.zext(k));
#ifdef  DEBUG_CAST
	  dbgs() << "ZExt([" << a << "," << b << "]," << k << ")=" << Tmp << "\n"; 
#endif 	
	  // GeneralizedJoin does not help since we have at most two
	  // intervals to be joined.
	  LHS->join(&Tmp);
	}
      }
      break;
    case Instruction::SExt:  
      {  
	unsigned k;
	Utilities::getIntegerWidth(I.getType(),k);
	// **NORTH POLE SPLIT** and compute signed extension for each of
	// the two elements and then lubbing them
	std::vector<WrappedRangePtr> s = 
	  nsplit(RHS->getLB(), RHS->getUB(), RHS->getLB().getBitWidth());
	WrappedRange Tmp(*LHS);
	LHS->makeBot();  
	typedef std::vector<WrappedRangePtr>::iterator It;
	for (It I=s.begin(), E=s.end(); I!=E; ++I){
	  APInt a = (*I).get()->getLB();
	  APInt b = (*I).get()->getUB();
	  Tmp.setLB(a.sext(k));
	  Tmp.setUB(b.sext(k));    
#ifdef  DEBUG_CAST
	  dbgs() << "SExt([" << a << "," <<  b << "]," << k << ")=" << Tmp << "\n"; 
#endif 	
	  // GeneralizedJoin does not help since we have at most two
	  // intervals to be joined.
	  LHS->join(&Tmp);
	}
      }
      break;    
    default:; // bitcast are non-op
    } // end switch
  }
  
  if (!V) delete RHS;
   LHS->normalizeTop();    
  DEBUG(dbgs() << "\t[RESULT]");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");      
  return LHS;
}

void WrappedRange::WrappedLogicalBitwise(WrappedRange *LHS, 
					 WrappedRange *Op1, WrappedRange *Op2,
					 unsigned Opcode){
 
  // General case: **SOUTH POLE SPLIT** and compute operation for each
  // of the elements and then lubbing them

  std::vector<WrappedRangePtr> s1 = 
    ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth());
  std::vector<WrappedRangePtr> s2 = 
    ssplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth());

  LHS->makeBot(); 
  typedef std::vector<WrappedRangePtr>::iterator It;
  for (It I1 = s1.begin(), E1 =s1.end(); I1 != E1; ++I1){
    for (It I2 = s2.begin(), E2 =s2.end(); I2 != E2; ++I2){
      switch(Opcode){
      case Instruction::Or:
	{
	  APInt lb; APInt ub;
	  unimelb::unsignedOr((*I1).get(), (*I2).get(), lb, ub);
	  WrappedRange Tmp(lb, ub, Op1->getLB().getBitWidth());
#ifdef DEBUG_LOGICALBIT
	  dbgs() << "OR(" << *((*I1).get()) << "," <<  *((*I2).get()) << ") = "
		 << Tmp << "\n";
#endif 
	  // FIXME: we could use GeneralizedJoin to be more precise.
	  LHS->join(&Tmp);
	}
	break;
      case Instruction::And:
	{
	  APInt lb; APInt ub;
	  unimelb::unsignedAnd((*I1).get(), (*I2).get(), lb, ub);
	  WrappedRange Tmp(lb, ub, Op1->getLB().getBitWidth());
#ifdef DEBUG_LOGICALBIT
	  dbgs() << "AND(" << *((*I1).get()) << "," <<  *((*I2).get()) << ") = "
		 << Tmp << "\n";
#endif 
	  // FIXME: we could use GeneralizedJoin to be more precise.
	  LHS->join(&Tmp);
	}
	break;
      case Instruction::Xor:
	{
	  APInt lb; APInt ub;
	  unimelb::unsignedXor((*I1).get(),(*I2).get(), lb, ub);
	  WrappedRange Tmp(lb,ub,Op1->getLB().getBitWidth());
#ifdef DEBUG_LOGICALBIT
	  dbgs() << "XOR(" << *((*I1).get()) << "," <<  *((*I2).get()) << ") = "
		 << Tmp << "\n";
#endif 
	  // FIXME: we could use GeneralizedJoin to be more precise.
	  LHS->join(&Tmp);
	}
	break;
      default:
	llvm_unreachable("Unexpected instruction");
      } // end switch
#ifdef DEBUG_LOGICALBIT
      dbgs() << "After intermediate join: " << *LHS << "\n";
#endif 
    }
  }
#ifdef DEBUG_LOGICALBIT
    dbgs() << "After lubbing "; LHS->print(dbgs()); dbgs() << "\n";
#endif 
}

// Pre: Operand is not bottom
void WrappedRange::
WrappedBitwiseShifts(WrappedRange *LHS, 
		     WrappedRange *Operand, WrappedRange *Shift,
		     unsigned Opcode){
		     
  #ifdef DEBUG_SHIFTS
  dbgs() << "Trying to Op:" << Opcode << ": For : " << *Operand  <<", shift:" << *Shift << "\n";
  #endif
  
  switch(Opcode){
  case Instruction::Shl:    
    // The main idea of Shl is to check whether the lower w-k bits of
    // the Operand are equal to the Operand. If yes, Shl can be done
    // safely. Otherwise, we return the interval [0,1^{w-k}0^{k}]
    if (Shift->IsConstantRange()){
      APInt k = Shift->getUB();
      unsigned NumBitsSurviveShift = k.getBitWidth() - k.getZExtValue();
      WrappedRange *Tmp = new WrappedRange(*Operand);
      Truncate(Tmp, Operand, NumBitsSurviveShift);
      APInt a(Operand->getLB());
      APInt b(Operand->getUB());
      // Be careful: Truncate will reduce the width of Tmp.  To compare
      // with a and b we need to pad 0's or 1's so that all of them have the
      // same width again.
      APInt c(k.getBitWidth(), Tmp->getLB().getSExtValue(), false);
      APInt d(k.getBitWidth(), Tmp->getUB().getSExtValue(), false);
      assert(a.getBitWidth() == c.getBitWidth() && 
	     b.getBitWidth() == d.getBitWidth());
#ifdef DEBUG_SHIFTS
      dbgs() << "[" << a << "," << b << "] =? ";
      dbgs() << "[" << c << "," << d << "]\n";
      dbgs() << "BINARY \n";
      dbgs() << "[" << a.toString(2,false) << "," << b.toString(2,false) << "] =?\n";
      dbgs() << "[" << c.toString(2,false) << "," << d.toString(2,false) << "]\n";
#endif 
      if (!Tmp->IsTop() && (a == c) && (b == d)){
	// At this point the shift will not through away relevant bits
	// so it is safe to shift on the left.
	LHS->setLB(a << k);
	LHS->setUB(b << k);    
      }
      else{
	// 000.......0
	LHS->setLB(APInt::getNullValue(a.getBitWidth())); 
	// 1111...0000 where the number of 1's is w-k.
	LHS->setUB(APInt::getHighBitsSet(a.getBitWidth(), NumBitsSurviveShift));  
      }
#ifdef DEBUG_SHIFTS
      dbgs() << "RESULT:" << *LHS << " BINARY: ";
      dbgs () << "[" << LHS->getLB().toString(2,false) << "," 
	      << LHS->getUB().toString(2,false) << "]\n";
#endif 
      delete Tmp;
    }
    else{
      // FIXME: NOT_IMPLEMENTED. The shift cannot be inferred as a
      // constant at compile time
      LHS->makeTop();
    }
    break;
  case Instruction::LShr:
    if (Shift->IsConstantRange()){
      APInt k = Shift->getUB();
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();	
      /// If SOUTH POLE \in [a,b] then [0^w, 0^k 1^{w-k}]  (rule 1) 
      /// otherwise [ a >>_l k, b >>_l k]                  (rule 2)
      ///
      /// The range crosses the south pole.  E.g., if we shift
      /// logically two bits each bound of the range [0011,0001] to
      /// the right we would get [0000,0000]. However, assume that the
      /// exact value is 1111 (which is included in that range) and
      /// shift logically two bits to the right. We would get 0011 !
      /// To cover this case we have rule 1.
      if (Operand->IsTop() || CrossSouthPole(a,b)){
#ifdef DEBUG_SHIFTS
	dbgs() << "The operand is crossing the south pole\n";
#endif 
	// 0.......0
	LHS->setLB(APInt::getNullValue(a.getBitWidth()));
	// 0..01...1 where the number of 1's is w-k
	LHS->setUB(APInt::getLowBitsSet(a.getBitWidth(), 
					a.getBitWidth() - k.getZExtValue())); 
      }
      else{
	LHS->setLB(a.lshr(k));
	LHS->setUB(b.lshr(k));    
      }
#ifdef DEBUG_SHIFTS
      dbgs() << *LHS << "\n";
      dbgs () << "[" << LHS->getLB().toString(2,false) << "," 
	      << LHS->getUB().toString(2,false) << "]\n";
#endif 
    }
    else{
      // FIXME: NOT_IMPLEMENTED.  The shift cannot be inferred as a
      // constant at compile time.
      LHS->makeTop();
    }
    break;
  case Instruction::AShr:
    if (Shift->IsConstantRange()){
      APInt k = Shift->getUB();
      APInt a = Operand->getLB();
      APInt b = Operand->getUB();	
      /// If NORTH POLE \in [a,b] then [1^{k}0^{w-k}, 0^k 1^{w-k}]  (rule 1) 
      /// otherwise                    [ a >>_a k, b >>_a k]        (rule 2)
      ///
      if (Operand->IsTop() || CrossNorthPole(a,b)){
#ifdef DEBUG_SHIFTS
	dbgs() << "The operand is crossing the north pole\n";
#endif 
	// lower bound is 1...10....0 where the number of 1's is k.
	LHS->setLB(APInt::getHighBitsSet(a.getBitWidth(), 
					 k.getZExtValue()));  
	// upper bound is 0..01...1 where the number of 1's is w-k
	LHS->setUB(APInt::getLowBitsSet(b.getBitWidth(), 
					b.getBitWidth() - k.getZExtValue()));    
      }
      else{
	LHS->setLB(a.ashr(k));
	LHS->setUB(b.ashr(k));    
      }
#ifdef DEBUG_SHIFTS
      dbgs() << *LHS << "\n";
      dbgs () << "[" << LHS->getLB().toString(2,false) << "," 
	      << LHS->getUB().toString(2,false) << "]\n";
#endif 
    }
    else{
      // FIXME: NOT_IMPLEMENTED. The shift cannot be inferred as a
      // constant at compile time.
      LHS->makeTop();
    }
    break;
  default:
    llvm_unreachable("Unexpected instruction");
  } // end switch
}


/// Perform the transfer function for bitwise  operations. 
AbstractValue* WrappedRange::
visitBitwiseBinaryOp(AbstractValue * V1, 
		     AbstractValue * V2, 
		     const Type * Op1Ty, const Type * Op2Ty, 
		     unsigned OpCode   , const char * OpCodeName){
  
  WrappedRange *Op1 = cast<WrappedRange>(V1);
  WrappedRange *Op2 = cast<WrappedRange>(V2);
  WrappedRange *LHS = new WrappedRange(*this);

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
      WrappedRange Tmp(*Op1);
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

#ifdef DEBUG_LOGICALBIT
      dbgs() << "Operand 1 is top\n";
#endif 
      WrappedLogicalBitwise(LHS, &Tmp, Op2, OpCode);	  
    }      
    else if (Op2->IsTop()){
#ifdef DEBUG_LOGICALBIT
      dbgs() << "Operand 2 is top\n";
#endif 
      WrappedRange Tmp(*Op2);
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
    
    WrappedBitwiseShifts(LHS, Op1, Op2,OpCode);
    break;
  default:;
  } // end switch

  LHS->normalizeTop();    
  DEBUG(LHS->printRange(dbgs())); 
  DEBUG(dbgs() << "\n");        
  return LHS;  
}


// Tests

void test_GeneralizedJoin(){
  {
    APInt a(8,  2,false);  APInt b(8, 10,false);
    APInt c(8,120,false);  APInt d(8,130,false);
    APInt e(8,132,false);  APInt f(8,135,false);
    APInt zero(8,0,false); 
    // Temporary constructors
    AbstractValue * R1 = dyn_cast<AbstractValue>(new WrappedRange(a,b,a.getBitWidth()));
    AbstractValue * R2 = dyn_cast<AbstractValue>(new WrappedRange(c,d,c.getBitWidth()));
    AbstractValue * R3 = dyn_cast<AbstractValue>(new WrappedRange(e,f,e.getBitWidth()));
    std::vector<AbstractValue*> vv;
    vv.push_back(R3); vv.push_back(R2); vv.push_back(R1);
    WrappedRange * Res = new WrappedRange(zero,zero,zero.getBitWidth());  
    Res->GeneralizedJoin(vv);
    // it should be [2,135]
    dbgs()<< "Result for test 1: " ;
    dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10,false) << "]\n";
  }

  {
    APInt a(8,   1 , false);  APInt b(8,  10 , false);
    APInt c(8, 120 , false);  APInt d(8, 130 , false);
    APInt e(8, 132 , false);  APInt f(8, 135 , false);
    APInt g(8, 220 , false);  APInt h(8,  50 , false);

    APInt zero(8, 0, false); 
    // Temporary constructors
    AbstractValue * R1 = dyn_cast<AbstractValue>(new WrappedRange(a,b,a.getBitWidth()));
    AbstractValue * R2 = dyn_cast<AbstractValue>(new WrappedRange(c,d,c.getBitWidth()));
    AbstractValue * R3 = dyn_cast<AbstractValue>(new WrappedRange(e,f,e.getBitWidth()));
    AbstractValue * R4 = dyn_cast<AbstractValue>(new WrappedRange(g,h,g.getBitWidth()));
    std::vector<AbstractValue*> vv;
    vv.push_back(R3); vv.push_back(R4); vv.push_back(R2); vv.push_back(R1);
    WrappedRange * Res = new WrappedRange(zero,zero,zero.getBitWidth());  
    Res->GeneralizedJoin(vv);
    // it should be [220,135]
    dbgs()<< "Result for test 2: " ;
    dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10, false) << "]\n";
  }

  {
    APInt a(3,   0 , false);  APInt b(3,   1 , false);
    APInt c(3,   7 , false);  APInt d(3,   0 , false);
    APInt e(3,   6 , false);  APInt f(3,   7 , false);
    APInt zero(3, 0, false); 
    // Temporary constructors
    AbstractValue * R1 = dyn_cast<AbstractValue>(new WrappedRange(a,b,a.getBitWidth()));
    AbstractValue * R2 = dyn_cast<AbstractValue>(new WrappedRange(c,d,c.getBitWidth()));
    AbstractValue * R3 = dyn_cast<AbstractValue>(new WrappedRange(e,f,e.getBitWidth()));
    AbstractValue * R4 = dyn_cast<AbstractValue>(new WrappedRange(a,b,a.getBitWidth()));
    std::vector<AbstractValue*> vv;
    // vv.push_back(R3); vv.push_back(R4); vv.push_back(R2); vv.push_back(R1);
    vv.push_back(R1); vv.push_back(R2); vv.push_back(R3); vv.push_back(R4);
    WrappedRange * Res = new WrappedRange(zero,zero,zero.getBitWidth());  
    Res->GeneralizedJoin(vv);
    // it should be [6,1]
    dbgs()<< "Result for test 3: " ;
    dbgs() << "[" << Res->getLB().toString(10,false) << "," << Res->getUB().toString(10, false) << "]\n";
  }


}


				

