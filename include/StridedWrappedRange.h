// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __STRIDED_WRAPPED_RANGE__H__
#define __STRIDED_WRAPPED_RANGE__H__
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

#define round(x) ((x)>=0?(long)((x)+0.5):(long)((x)-0.5))

namespace unimelb {

  class StridedWrappedRange;
  typedef std::tr1::shared_ptr<StridedWrappedRange>  StridedWrappedRangePtr;

  class UtilFunctions {
    public:
        static uint64_t getGCD(uint64_t a, uint64_t b) {
            //dbgs() << "Calliing:" << a << ":" << b <<"\n";
            if(b==0) {
                return a;
            } else {
                return UtilFunctions::getGCD(b, a % b);
            }
        }

        static unsigned long getLCM(unsigned long a, unsigned long b) {
            return (uint64_t)((uint64_t)a * (uint64_t)b) / UtilFunctions::getGCD(a, b);
        }

        static unsigned long getExtendedGCD(unsigned long a, unsigned long b, unsigned long *x, unsigned long *y) {
            unsigned long x0, y0, d;
            if(b == 0) {
                *x = 1;
                *y = 0;
                return a;
            }
            d = UtilFunctions::getExtendedGCD(b, a%b, &x0, &y0);
            *x = y0;
            *y = x0 - ((a/b) * y0);
            return d;
        }
        
        /*static long getIGCD(long a, long b) {
            long ai, bi, temp;
            ai = a;
            bi = b;
            dbgs() << "GOT:" << a << ":" << b <<"\n";
            if(bi < 0) {
                dbgs() << "IN IF:" << ":" << bi <<"\n";
                bi = -1 * bi;
                dbgs() << "OUT IF:" << ":" << bi <<"\n";
            }
            dbgs() << "After conv:" << bi << "\n";
            while(bi) {
                temp = bi;
                bi = ai % bi;
                ai = temp;
            }
            if(ai == 1 || bi == 1) {
                dbgs() << "Returning 1\n";
                return 1;
            }
            dbgs() << "Returning:" << ai << "\n";
            return ai;
        }*/

        static bool get_intersection(float a, float b, int a_dir, int b_dir, float *lb, float *ub) {
            if(a_dir == 2 && b_dir == 2) {
                if(a > b) {
                    *lb = a;
                } else {
                    *lb = b;
                }
                *ub = 1.0 / 0;
                return true;
            }
            if(a_dir == 1 && b_dir == 2) {
                if(a > b) {
                    *lb = b;
                    *ub = a;
                    return true;
                }
                return false;
            }
            if(a_dir == 2 && b_dir == 1) {
                if(b > a) {
                    *lb = a;
                    *ub = b;
                    return true;
                }
                return false;
            }
            if(a_dir == 1 && b_dir == 1) {
                if(a < b) {
                    *ub = a;
                } else {
                    *ub = b;
                }
                *lb = -1.0 / 0;
                return true;
            }
            return false;
        }        

        static bool diophantineNaturalSolution(long c, long a, long b, float *solx, float *soly) {

            long d, x0, y0;
            uint64_t tmp_g;
            //dbgs() << "DIOPHANTIONE:" << c << ":" << a << ":" << b << "\n";
            //dbgs() << "DIOPHANTIONE:" << b << ":" << c << "\n";
            //dbgs() << UtilFunctions::getGCD((uint64_t)b, (uint64_t)c) << "\n";
            //dbgs() << "DIOPHANTIONE END:" << c << ":" << a << ":" << b << "\n";
            tmp_g = UtilFunctions::getGCD((uint64_t)b, (uint64_t)c);
            //dbgs() << "DIOPHANITE 2:" << a << ":" << tmp_g << "\n";
            
            d = UtilFunctions::getGCD(a, tmp_g);
            a = a / d;
            b = b / d;
            c = c / d;
            if(c == 0) {
                *solx = 0;
                *soly = 0;
                return true;
            }
            
            //dbgs() << "DIOPHANTIONE1:" << a << ":" << b << ":" << c << "\n";
            
            d = UtilFunctions::getExtendedGCD((unsigned long)a, (unsigned long)b, (unsigned long *)&x0, (unsigned long *)&y0);
            //dbgs() << "DIOPHANTIONE111:" << a << ":" << b << ":c=" << c << ":d=" << d << ":" << tmp_g <<"\n";

            if(((int64_t)c)%d == 0) {
                //dbgs() << "DIOPHANTIONE2:" << a << ":" << b << ":" << c << "\n";
                float t0, t1, t, lb, ub;
                int t0_dir, t1_dir;
                
                t0 = ((-c * x0) * 1.0) / b;
                t1 = ((c * y0) * 1.0) / a;
                if(b < 0) {
                    t0_dir = 1;
                } else {
                    t0_dir = 2;
                }
                if(a < 0) {
                    t1_dir = 2;
                } else {
                    t1_dir = 1;
                }
                if(UtilFunctions::get_intersection(t0, t1, t0_dir, t1_dir, &lb, &ub)) {
                    float lb_abs, ub_abs, pos_inf, neg_inf;
                    pos_inf = 1.0 / 0;
                    neg_inf = -1.0 / 0;
                    lb_abs = lb;
                    if(lb < 0) {
                        lb_abs = -1 * lb;
                    }
                    ub_abs = ub;
                    if(ub < 0) {
                        ub_abs = -1 * ub;
                    }
                
                    if(lb <= 0 && ub >=0) {
                        t = lb;
                        if(ub_abs < lb_abs) {
                            t = ub;
                        }
                    } else if(lb == pos_inf || lb == neg_inf) {
                        t = ub;
                    } else if(ub == pos_inf || ub == neg_inf) {
                        t = lb;
                    } else {
                        t = lb;
                        if(ub_abs < lb_abs) {
                            t = ub;
                        }
                    }
                    if(t == ub) {
                        
                    } else {
                    }
                    *solx = c*x0 + b*t;
                    *soly = c*y0 - a*t;
                } else {
                    return false;
                }
                return true;
            }
            //dbgs() << "HIDSOSDOSDSO\n";
            return false;
            
        }
  };

  class StridedWrappedRange: public BaseRange {
  public:
    //unsigned long stride_val=1;           
    virtual BaseId getValueID() const { return StridedWrappedRangeId; }
    /// Constructor of the class.
    StridedWrappedRange(Value *V):  
      BaseRange(V, __SIGNED, false), 
      __isBottom(false),
      CounterWideningCannotDoubling(0){
      
    }
    
    /// Constructor of the class for an integer constant.
    StridedWrappedRange(const ConstantInt *C, unsigned Width): 
      BaseRange(C,Width, __SIGNED, false), 
      __isBottom(false),
      CounterWideningCannotDoubling(0){
      setStride(0);      
    }

    /// Constructor of the class for a TBool object 
    StridedWrappedRange(Value *V, TBool * B):
      BaseRange(V, __SIGNED, false), 
      __isBottom(false),
      CounterWideningCannotDoubling(0){
      if (B->isTrue()){
	setLB((uint64_t) 1); 
	setUB((uint64_t) 1);
      setStride(0);
      }
      else if (B->isFalse()){
	setLB((uint64_t) 0); 
	setUB((uint64_t) 0);
      setStride(0);
      }
      else{
	setLB((uint64_t) 0); 
	setUB((uint64_t) 1);
      setStride(1);
      }
      
    }

    /// Constructor of the class for APInt's 
    /// For temporary computations.
    StridedWrappedRange(APInt lb, APInt ub, unsigned Width): 
      BaseRange(lb,ub,Width,__SIGNED,false),
      __isBottom(false),
      CounterWideningCannotDoubling(0){ 
      
    }

    StridedWrappedRange(APInt lb, APInt ub, unsigned Width, unsigned long new_stride): 
      BaseRange(lb,ub,Width,__SIGNED,false),
      __isBottom(false),
      CounterWideningCannotDoubling(0){
      if(lb == ub) {
        setStride(0);
      } else {
        setStride(new_stride);
      }
    }

    /// Copy constructor of the class.
    StridedWrappedRange(const StridedWrappedRange& other ): BaseRange(other){
      __isBottom = other.__isBottom;
      CounterWideningCannotDoubling = other.CounterWideningCannotDoubling;
    }

    /// Destructor of the class.
    ~StridedWrappedRange(){}

    /// Cardinality of a wrapped interval.
    static inline APInt WCard(const APInt &x, const APInt &y){
    
      //unsigned long newbw;
      //newbw = (x.getBitWidth() < y.getBitWidth()? y.getBitWidth(): x.getBitWidth());
    
      //APInt tx(newbw, x.getZExtValue());
      //APInt ty(newbw, y.getZExtValue());
      
      if (x == y+1){  // ie., if [MININT,MAXINT}
	APInt card = APInt::getMaxValue(x.getBitWidth());
	// FIXME: getMaxValue(width) is actually 2^w - 1. 
	// It should be card here 2^w
	//dbgs() << " CARD Retunring 1:" << card << "\n";
	return card;
      }
      else{
	// Implicitly we use mod 2^w where w is the width of x and y.
	// since APInt will wraparound if overflow.
	APInt card = (y - x) + 1;
	//dbgs() << " CARD Returning 2:" << card << "\n";
	//APInt ret_val(card.getBitWidth() + 1, card.getZExtValue());
	return card; 
      }
    }
    
    static inline uint64_t WCard_mod(const APInt &x, const APInt &y) {
        int64_t x_s = x.getSExtValue();
        int64_t y_s = y.getSExtValue();
        
        //dbgs() << "X_S=" << x_s << ", y_s=" << y_s << "\n";
        y_s = (int64_t)(y_s + 1);
        
        if(x_s == y_s) {
          uint64_t val_n = APInt::getMaxValue(x.getBitWidth()).getZExtValue();  
          //dbgs() << "Returning from here:" << val_n << "\n";
          return val_n + (uint64_t)1;
        } else {
            APInt ret_val = WCard(x, y);
            if(ret_val == APInt::getMaxValue(x.getBitWidth())) {
                //uint64_t my_val = ret_val.getZExtValue() + 1;
                //dbgs() << "WCARD_MOD RERUGNING:" << my_val << "\n";
                return ret_val.getZExtValue();
            }
            return ret_val.getZExtValue();
        }
    }
    /// To try to have a single representation of top (e.g., [1,0],
    /// [2,1], [-1,-2], [MININT,MAXINIT], etc). This is not needed for
    /// correctness but it is vital for presentation and a fair
    /// comparison with other analyses.
    inline void normalizeTop(){
      if (isBot()) return;
      if (IsTop()) {
        setStride(1); return;
      }
      
      //correct stride
      if(getStride() == 0 && getLB() != getUB()) {
        setStride(1);
      }
      
      
      APInt tLB(getWidth() + 1, LB.getZExtValue());
      APInt tUB(getWidth() + 1, UB.getZExtValue());

      if (((tLB == tUB+1) || (getLB() == (getUB() + 1))) && (getStride() <= 1)){ // implicitly using mod 2^w
      	//dbgs() << "Normalizing [" << LB << "," << UB << "]" << " to top interval (" << getWidth() << " bits).\n";
      	makeTop();
      }
      else if(LB == UB) {
        setStride(0);
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
      unsigned long curr_str = getStride();
      APInt x = getLB();
      APInt y = getUB();
      if (IsTop() || (x == y+1)) {
	APInt card = APInt::getMaxValue(width);
	    if(curr_str == 0) {
    	return card.getZExtValue() + 1;
	    }
	    return (card.getZExtValue() + 1) / curr_str;
      }	
      APInt card = (y - x + 1);
      if(curr_str == 0) {
        return card.getZExtValue();
      }
      return card.getZExtValue() / curr_str;
    }

    /// Return true if | \gamma(this) | == 1 
    virtual bool isGammaSingleton() const {
      if (isBot() || IsTop()) return false;
      APInt lb  = getLB();
      APInt ub  = getUB();
      APInt card  = StridedWrappedRange::WCard(lb,ub);
      return (card == 1);
    }

    

    inline bool isSingleVal() const {
        if(IsTop() || isBot()) return false;
        return getLB().getZExtValue() == getUB().getZExtValue();
    }

    inline bool IsRangeTooBig(const APInt &lb, const APInt &ub){
      APInt card  = StridedWrappedRange::WCard(lb,ub);
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
    StridedWrappedRange* clone(){
      return new StridedWrappedRange(*this);
    }

    /// Methods for support type inquiry through isa, cast, and
    /// dyn_cast.
    static inline bool classof(const StridedWrappedRange *) { 
      return true; 
    }
    static inline bool classof(const BaseRange *V) {
      return (V->getValueID() == StridedWrappedRangeId);
    }
    static inline bool classof(const AbstractValue *V) {
      return (V->getValueID() == StridedWrappedRangeId);
    }

    virtual bool isBot() const; 
    virtual bool IsTop() const ; 
    virtual void makeBot();
    virtual void makeTop();
    virtual void print(raw_ostream &Out) const;
    void AdjustStride();

    inline void WrappedRangeAssign(StridedWrappedRange * other) {
      BaseRange::RangeAssign(other);
      __isBottom = other->__isBottom;
    }

    /// Key auxiliary methods to split the wrapped range at the south
    /// and north poles. The use of these guys are key for most of the
    /// arithmetic, casting and bitwise operations as well as comparison
    /// operators.
    static std::vector<StridedWrappedRangePtr> ssplit(const APInt&, const APInt&, unsigned);
    static std::vector<StridedWrappedRangePtr> strided_ssplit(const APInt&, const APInt&, unsigned, unsigned long);
    static std::vector<StridedWrappedRangePtr> nsplit(const APInt&, const APInt&, unsigned);
    static std::vector<StridedWrappedRangePtr> strided_nsplit(const APInt&, const APInt&, unsigned, unsigned long);
    
    static bool minimal_common_integer(StridedWrappedRange *Op1, StridedWrappedRange *Op2, APInt *result);
    static bool minimal_common_integer_splitted(StridedWrappedRange *Op1, StridedWrappedRange *Op2, APInt *result);
    static std::vector<StridedWrappedRangePtr> MultiValueIntersection(StridedWrappedRange *Op1, StridedWrappedRange *Op2);
    static bool StridedGeneralizedJoin(std::vector<AbstractValue *> Values, StridedWrappedRange *result);
    
    static StridedWrappedRange StridedLogicalBitwiseOr(StridedWrappedRange *Op1, StridedWrappedRange *Op2);
    static StridedWrappedRange StridedLogicalBitwiseNot(StridedWrappedRange *Op1);
    
    static StridedWrappedRange StridedShl(StridedWrappedRange *Op, uint64_t val);
    
    static StridedWrappedRange StridedAShr(StridedWrappedRange *Op, uint64_t val);
    static StridedWrappedRange StridedLShr(StridedWrappedRange *Op, uint64_t val);

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

    /// To filter the interval of a variable involved in a guard.
    virtual void filterSigma(unsigned, AbstractValue*, AbstractValue*);
    void filterSigma_TwoVars(unsigned, StridedWrappedRange*, StridedWrappedRange*);
    void filterSigma_VarAndConst(unsigned, StridedWrappedRange*, StridedWrappedRange*);


    // Here abstract domain-dependent transfer functions
    void WrappedPlus(StridedWrappedRange *,
		     const StridedWrappedRange *, const StridedWrappedRange *);
    void WrappedMinus(StridedWrappedRange *,
		      const StridedWrappedRange *, const StridedWrappedRange *);
    void WrappedMultiplication(StridedWrappedRange *,
			       const StridedWrappedRange *, const StridedWrappedRange *);
    void WrappedDivision(StridedWrappedRange *, 
			 const StridedWrappedRange *, const StridedWrappedRange *, bool);    
    void WrappedRem(StridedWrappedRange *, 
		    const StridedWrappedRange *,const StridedWrappedRange *, bool);
    // Machiry: Check if current value is more precise
    bool isMoreOrEqualPrecise(AbstractValue *);    

    // addition, substraction, and the rest above
    virtual AbstractValue* visitArithBinaryOp(AbstractValue *, AbstractValue *,
					      unsigned, const char *);
    // truncation, signed/unsigned extension
    virtual AbstractValue* visitCast(Instruction &, AbstractValue *, TBool *, bool);
    // and, or, xor 
    void WrappedLogicalBitwise(StridedWrappedRange *, 
			       StridedWrappedRange *, StridedWrappedRange *,
			       unsigned);    
    // logical/arithmetic right shift, left shift
    void  WrappedBitwiseShifts(StridedWrappedRange *,  StridedWrappedRange *, StridedWrappedRange *,
			       unsigned);

    void  StridedWrappedBitwiseShitfs(StridedWrappedRange *,  StridedWrappedRange *, StridedWrappedRange *,
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
    void Binary_WrappedJoin(StridedWrappedRange *R1, StridedWrappedRange *R2);
    
    

  };

  inline raw_ostream& operator<<(raw_ostream& o, StridedWrappedRange r) {
    r.printRange(o);
    return o;
  }

  StridedWrappedRange StridedWrappedMeet(StridedWrappedRange *, StridedWrappedRange *);

  inline bool IsMSBOneSI(const APInt &x){
    // This tests the high bit of the APInt to determine if it is set.
    return (x.isNegative());
    }
  
  inline bool IsMSBZeroSI(const APInt &x){
    return (!x.isNegative());
  }
  
  /// Return true if x is lexicographically smaller than y.
  inline bool SILex_LessThan(const APInt &x, const APInt &y){
    bool a = !x.isNegative(); //IsMSBZero(x);
    bool b = !y.isNegative(); //IsMSBZero(y);
    if (!a &&  b) return false;
    else if ( a && !b) return true;
    else if (!a && !b) return x.slt(y);
    else {
    return x.ult(y);      
    }
  }
  
  /// Return true if x is lexicographically smaller or equal than y.
  inline bool SILex_LessOrEqual(const APInt &x, const APInt &y){
    bool a = !x.isNegative(); //IsMSBZero(x);
    bool b = !y.isNegative(); //IsMSBZero(y);
    if (!a &&  b) return false;
    else if ( a && !b) return true;
    else if (!a && !b) {
    return x.sle(y);
    }
    else {
    return x.ule(y);
    }
  }
  
  /// Lexicographical maximum
  inline  APInt Lex_maxSI(const APInt &x, const APInt &y){
    return (SILex_LessOrEqual(x,y)? y : x);
  }
  
  /// Lexicographical minimum
  /*inline  APInt Lex_min(const APInt &x, const APInt &y){
    return (Lex_LessOrEqual(x,y)? x : y);
  }*/

  /// Return a wrapped interval that covers singleton x and y.
  inline StridedWrappedRange 
  simkSmallerInterval(const APInt &x, const APInt &y, unsigned width){
    StridedWrappedRange R1(x, x, width);    
    StridedWrappedRange R2(y, y, width);    
    R1.join(&R2);
    return R1;
  }

} // end namespace

#endif
