// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __WRAPPED_RANGE__H__
#define __WRAPPED_RANGE__H__
////////////////////////////////////////////////////////////////////////
/// \file  WrappedRange.h
///        Wrapped Interval Abstract Domain.
///
/// This file contains the definition of the WrappedRange class,
/// which improves the Range class by allowing an interval to
/// be wrapped around without directly going to "top". 
///
/// Moreover, very importantly this analysis is sign-agnostic. That
/// is, it does not make any assumption about sign of variables in
/// opposite to Range and BaseRange classes. However, the abstract
/// domain does not form a lattice so special care is needed since
/// joins and meets are neither monotone nor associate.
///
/// For details, we refer to "Signedness-Agnostic Program Analysis:
/// Precise Integer Bounds for Low-Level Code" by J. A. Navas,
/// P. Schachte, H. Sondergaard, P. J. Stuckey published in APLAS'12.
/// 
/// We need a special symbol for bottom since the range [-1,0] is a
/// valid wrapped interval that, in fact, it denotes top.
////////////////////////////////////////////////////////////////////////

#include "AbstractValue.h"
#include "BaseRange.h"
#include "Support/Utils.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/Attributes.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/Statistic.h"

#include <tr1/memory>

/// Wrapped intervals do not make any distinction whether variables
/// are signed or not since the analysis is signed-agnostic.
/// Therefore, by default we assume that all operations are unsigned
/// except those that really depend on the sign (e.g. division,
/// comparisons, etc). In any case, the analysis uses this flag.
#define __SIGNED false  // false means unsigned by default.
#define DEBUG_TYPE "RangeAnalysis"

namespace unimelb {

  class WrappedRange;
  typedef std::tr1::shared_ptr<WrappedRange>  WrappedRangePtr;

  class WrappedRange: public BaseRange {
  public:      
    virtual BaseId getValueID() const { return WrappedRangeId; }
    /// Constructor of the class.
    WrappedRange(Value *V):  
      BaseRange(V, __SIGNED, false), 
      __isBottom(false),
      CounterWideningCannotDoubling(0){}
    
    /// Constructor of the class for an integer constant.
    WrappedRange(const ConstantInt *C, unsigned Width): 
      BaseRange(C,Width, __SIGNED, false), 
      __isBottom(false),
      CounterWideningCannotDoubling(0){ 
      
    }

    /// Constructor of the class for a TBool object 
    WrappedRange(Value *V, TBool * B):
      BaseRange(V, __SIGNED, false), 
      __isBottom(false),
      CounterWideningCannotDoubling(0){
      if (B->isTrue()){
	setLB((uint64_t) 1); 
	setUB((uint64_t) 1);
      }
      else if (B->isFalse()){
	setLB((uint64_t) 0); 
	setUB((uint64_t) 0);
      }
      else{
	setLB((uint64_t) 0); 
	setUB((uint64_t) 1);
      }
    }

    /// Constructor of the class for APInt's 
    /// For temporary computations.
    WrappedRange(APInt lb, APInt ub, unsigned Width): 
      BaseRange(lb,ub,Width,__SIGNED,false),
      __isBottom(false),
      CounterWideningCannotDoubling(0){ 
      
    }

    /// Copy constructor of the class.
    WrappedRange(const WrappedRange& other ): BaseRange(other){
      __isBottom = other.__isBottom;
      CounterWideningCannotDoubling = other.CounterWideningCannotDoubling;
    }

    /// Destructor of the class.
    ~WrappedRange(){}

    /// Cardinality of a wrapped interval.
    static inline APInt WCard(const APInt &x, const APInt &y){
      if (x == y+1){  // ie., if [MININT,MAXINT}
	APInt card = APInt::getMaxValue(x.getBitWidth());
	// FIXME: getMaxValue(width) is actually 2^w - 1. 
	// It should be card here 2^w
	return card;
      }
      else{
	// Implicitly we use mod 2^w where w is the width of x and y.
	// since APInt will wraparound if overflow.
	APInt card = (y - x) + 1;
	return card; 
      }
    }

    /// To try to have a single representation of top (e.g., [1,0],
    /// [2,1], [-1,-2], [MININT,MAXINIT], etc). This is not needed for
    /// correctness but it is vital for presentation and a fair
    /// comparison with other analyses.
    inline void normalizeTop(){
      if (isBot()) return;

      if (LB == UB+1){ // implicitly using mod 2^w
      	DEBUG(dbgs() << "Normalizing [" << LB << "," << UB << "]"
	             << " to top interval (" << getWidth() << " bits).\n");
      	makeTop();
      }
    }

    /// Used to compare precision with other analyses
    inline void normalize(){
      if (IsTop()) return;
      if (isBot()) return;
      normalizeTop();
    }

    // For comparison with other analyses.
    inline uint64_t Cardinality() const {
      if (isBot()) return 0;
      APInt x = getLB();
      APInt y = getUB();
      if (IsTop() || (x == y+1)) {
	APInt card = APInt::getMaxValue(width);
	return card.getZExtValue() + 1;
      }	
      APInt card = (y - x + 1);
      return card.getZExtValue();
    }

    /// Return true if | \gamma(this) | == 1 
    virtual bool isGammaSingleton() const {
      if (isBot() || IsTop()) return false;
      APInt lb  = getLB();
      APInt ub  = getUB();
      APInt card  = WrappedRange::WCard(lb,ub);
      return (card == 1);
    }

    inline bool IsRangeTooBig(const APInt &lb, const APInt &ub){
      APInt card  = WrappedRange::WCard(lb,ub);
      // If card does not fit into uint64_t then APInt raises an
      // exception.
      uint64_t n     =  card.getZExtValue();
      // If width of lb and ub are different then APInt raises an
      // exception.
      unsigned width = lb.getBitWidth();
      // If 2^w does not fit into uint64_t then APInt raises an exception.
      uint64_t Max = (APInt::getMaxValue(width)).getZExtValue() + 1;
      return (n >= Max);
    }

    inline void convertWidenBoundsToWrappedRange(const APInt &lb, const APInt &ub){
      if (IsRangeTooBig(lb,ub))
	makeTop();
      else{
	setLB(lb);
	setUB(ub);
      }
    }

    /// clone method
    WrappedRange* clone(){
      return new WrappedRange(*this);
    }

    /// Methods for support type inquiry through isa, cast, and
    /// dyn_cast.
    static inline bool classof(const WrappedRange *) { 
      return true; 
    }
    static inline bool classof(const BaseRange *V) {
      return (V->getValueID() == WrappedRangeId);
    }
    static inline bool classof(const AbstractValue *V) {
      return (V->getValueID() == WrappedRangeId);
    }

    virtual bool isBot() const; 
    virtual bool IsTop() const ; 
    virtual void makeBot();
    virtual void makeTop();
    virtual void print(raw_ostream &Out) const;

    inline void WrappedRangeAssign(WrappedRange * other) {
      BaseRange::RangeAssign(other);
      __isBottom = other->__isBottom;
    }

    /// Key auxiliary methods to split the wrapped range at the south
    /// and north poles. The use of these guys are key for most of the
    /// arithmetic, casting and bitwise operations as well as comparison
    /// operators.
    static std::vector<WrappedRangePtr> ssplit(const APInt&, const APInt&, unsigned);
    static std::vector<WrappedRangePtr> nsplit(const APInt&, const APInt&, unsigned);

    bool WrappedMember(const APInt&) const;
    
    virtual bool hasNoZero() const {
    	APInt zero(1, 0);
    	return !this->isBot() && !this->WrappedMember(zero);
    }

    bool WrappedlessOrEqual(AbstractValue *);
    virtual bool lessOrEqual(AbstractValue *);
    virtual void WrappedJoin(AbstractValue *);
    virtual void join(AbstractValue *);
    /// Apply the join but considering the fact that the domain is not
    /// associative. Thus, it may be more precise than apply simply
    /// join repeatedly. It can be used for operations like
    /// multiplication and phi nodes with multiple incoming values.
    virtual void GeneralizedJoin(std::vector<AbstractValue *>);
    virtual void meet(AbstractValue *, AbstractValue *);
    virtual bool isEqual(AbstractValue*);
    virtual void widening(AbstractValue *, const std::vector<int64_t> &);

    /// Return true is this is syntactically identical to V.
    virtual bool isIdentical(AbstractValue *V);

    /// To determine if the evaluation of a guard is true/false/maybe.
    virtual bool comparisonSle(AbstractValue *);
    virtual bool comparisonSlt(AbstractValue *);
    virtual bool comparisonUle(AbstractValue *);
    virtual bool comparisonUlt(AbstractValue *);
    
    bool isMoreOrEqualPrecise(AbstractValue *);

    /// To filter the interval of a variable involved in a guard.
    virtual void filterSigma(unsigned, AbstractValue*, AbstractValue*);
    void filterSigma_TwoVars(unsigned, WrappedRange*, WrappedRange*);
    void filterSigma_VarAndConst(unsigned, WrappedRange*, WrappedRange*);


    // Here abstract domain-dependent transfer functions
    void WrappedPlus(WrappedRange *,
		     const WrappedRange *, const WrappedRange *);
    void WrappedMinus(WrappedRange *,
		      const WrappedRange *, const WrappedRange *);
    void WrappedMultiplication(WrappedRange *,
			       const WrappedRange *, const WrappedRange *);
    void WrappedDivision(WrappedRange *, 
			 const WrappedRange *, const WrappedRange *, bool);    
    void WrappedRem(WrappedRange *, 
		    const WrappedRange *,const WrappedRange *, bool);    

    // addition, substraction, and the rest above
    virtual AbstractValue* visitArithBinaryOp(AbstractValue *, AbstractValue *,
					      unsigned, const char *);
    // truncation, signed/unsigned extension
    virtual AbstractValue* visitCast(Instruction &, AbstractValue *, TBool *, bool);
    // and, or, xor 
    void WrappedLogicalBitwise(WrappedRange *, 
			       WrappedRange *, WrappedRange *,
			       unsigned);    
    // logical/arithmetic right shift, left shift
    void  WrappedBitwiseShifts(WrappedRange *,  WrappedRange *, WrappedRange *,
			       unsigned);
    // all bitwise operations: many of them are quite tricky because
    // they are not monotone
    virtual AbstractValue*  visitBitwiseBinaryOp(AbstractValue *, AbstractValue *, 
						 const Type *, const Type *,
						 unsigned, const char *);

  private: 
    bool __isBottom; //!< If true the interval is bottom.

    // During widening it is possible that we cannot doubling the
    // interval but we could choose a program constant that may
    // produce a tighter interval. However, we can only do this a
    // finite number of times.
    unsigned int CounterWideningCannotDoubling;

    inline void resetBottomFlag(){
      __isBottom=false;
    }

    /// Convenient wrapper.
    void Binary_WrappedJoin(WrappedRange *R1, WrappedRange *R2);
    


  };

  

  WrappedRange WrappedMeet(WrappedRange *, WrappedRange *);
  
   inline raw_ostream& operator<<(raw_ostream& o, WrappedRange r) {
    r.printRange(o);
    return o;
  	}

  inline bool IsMSBOne(const APInt &x){
    // This tests the high bit of the APInt to determine if it is set.
    return (x.isNegative());
    }
  
  inline bool IsMSBZero(const APInt &x){
    return (!x.isNegative());
  }
  
  /// Return true if x is lexicographically smaller than y.
  inline bool Lex_LessThan(const APInt &x, const APInt &y){
    bool a = !x.isNegative(); //IsMSBZero(x);
    bool b = !y.isNegative(); //IsMSBZero(y);
    if (!a &&  b) return false;
    else if ( a && !b) return true;
    else if (!a && !b) return x.slt(y);
    else return x.ult(y);      
  }
  
  /// Return true if x is lexicographically smaller or equal than y.
  inline bool Lex_LessOrEqual(const APInt &x, const APInt &y){
    bool a = !x.isNegative(); //IsMSBZero(x);
    bool b = !y.isNegative(); //IsMSBZero(y);
    if (!a &&  b) return false;
    else if ( a && !b) return true;
    else if (!a && !b) return x.sle(y);
    else return x.ule(y);
  }
  
  /// Lexicographical maximum
  inline  APInt Lex_max(const APInt &x, const APInt &y){
    return (Lex_LessOrEqual(x,y)? y : x);
  }
  
  /// Lexicographical minimum
  inline  APInt Lex_min(const APInt &x, const APInt &y){
    return (Lex_LessOrEqual(x,y)? x : y);
  }

  /// Return a wrapped interval that covers singleton x and y.
  inline WrappedRange 
  mkSmallerInterval(const APInt &x, const APInt &y, unsigned width){
    WrappedRange R1(x, x, width);    
    WrappedRange R2(y, y, width);    
    R1.join(&R2);
    return R1;
  }

} // end namespace

#endif
