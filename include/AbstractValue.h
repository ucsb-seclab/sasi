// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __ABSTRACT_VALUE_H__
#define __ABSTRACT_VALUE_H__
////////////////////////////////////////////////////////////////////////////
/// \file AbstractValue.h
///       Abstract Lattice Value Interface.
///
/// This file contains the declaration of the AbstractValue
/// class, which is the base class to represent an element of an
/// abstract state.
/// 
/// An abstract state is a set of pairs <Var,Value_{bottom}> were
/// Value_{bottom} is the abstract value extended with the symbol
/// bottom. The set itself cannot be bottom.  Therefore if a block is
/// unreachable we may have multiple abstract states that represent
/// it.
////////////////////////////////////////////////////////////////////////////

#include "Support/TBool.h"
#include "llvm/Value.h"
#include "llvm/Constants.h"
#include "llvm/Type.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

using namespace llvm;
namespace unimelb {

  /// Hierarchy members that can be instantiated
  typedef enum {    
    RangeId               = 0, //!< classical range analysis.
    WrappedRangeId        = 1,  //!< wrapped range analysis.
    StridedWrappedRangeId        = 2  //!< wrapped range analysis.
  } BaseId ;

  /// Class that represents an abstract value.
  class AbstractValue {
  protected: 
    Value *var;           //!< variable associated with the abstract value.
    unsigned numOfChanges;//!< how many times the abstract value has been changed.     
    /// Block where the variable is defined. If a formal parameter
    /// then B is the first block of the function.
    BasicBlock *B;        //!< needed only if FixpointSSI
    bool IsLattice;       //!< whether the abstract domain is a lattice or not.
  public:      
    virtual BaseId getValueID() const = 0;

    /// Constructor of the class
    AbstractValue(Value *v, bool isLattice = true): 
      var(v), numOfChanges(0), B(NULL), IsLattice(isLattice){}   
    /// Constructor of the class. Only for temporary computations.
    AbstractValue(bool isLattice = true): 
      var(NULL), numOfChanges(0), IsLattice(isLattice){}       
    /// Copy constructor of the class
    AbstractValue(const AbstractValue&  other) {
      var          = other.var;
      numOfChanges = other.numOfChanges;
      B            = other.B;
      IsLattice    = other.IsLattice;
    }
    /// Make a clone of the abstract value
    virtual AbstractValue* clone() = 0;  
    /// Destructor of the class
    virtual ~AbstractValue(){}

    /// Return the number of times the variable has changed.
    inline unsigned  getNumOfChanges(){ return numOfChanges; }    
    /// Return a pointer to the Value associated with the abstract
    /// value. Return NULL if the value is a constant.
    inline Value*    getValue()         { return var; }
    inline Value*    getValue()   const { return var; }
    /// Return true if the variable is a constant.
    inline bool      isConstant() const { return (var == NULL); }
    /// Return true if the abstract domain is a lattice.
    inline bool      isLattice() const { 
      /// Currently, we return always true even if the underlying
      /// domain is not actually a lattice. This is sound but it may
      /// have negative consequences in terms of precision and
      /// termination during the fixpoint computation. For now, we
      /// take the risk.
      return true /*IsLattice*/; 
    }
    /// Return basic block associated with the variable (if fixpointSSI)
    inline BasicBlock* getBasicBlock() { return B;}

    /// Increment by one the number of changes.
    inline void incNumOfChanges(){ numOfChanges++;  }
    /// Reset to zero the number of changes.
    inline void resetNumOfChanges(){ numOfChanges=0;  }
    /// Method for support type inquiry through isa, cast, and
    /// dyn_cast.
    /// Set the basic block associated with the variable (if fixpointSSI)
    inline void setBasicBlock(BasicBlock *_B) { assert(!B); B=_B;}


    static inline bool classof(const AbstractValue *) { return true;}

    //////
    /// Standard abstract domain operations 
    //////

    /// Return true if |gamma(a)| = 1 where a is an abstract element.
    virtual bool isGammaSingleton() const = 0 ;

    /// Return true if the abstract value is bottom.
    virtual bool isBot() const = 0 ;
    /// Return true if the abstract value is top.
    virtual bool IsTop() const = 0 ;     
    
    virtual bool hasNoZero() const = 0;
    /// Make bottom the abstract value.
    virtual void makeBot() = 0;
    /// Make top the abstract value.
    virtual void makeTop() = 0;
    /// Join the abstract value V and this and store the result in
    /// this.
    virtual void join(AbstractValue * V) = 0;
    /// Special version to join multiple values if non-lattice domain.
    virtual void GeneralizedJoin(std::vector<AbstractValue *>) = 0;
    /// Meet two abstract values V1 and V2 and store the result in
    /// this.
    /// \todo It would be more convenient to be a friend
    virtual void meet(AbstractValue *V1, AbstractValue *V2) = 0;
    /// Return true if this is less or equal than V.
    virtual bool lessOrEqual(AbstractValue *V) = 0;
    /// Return true if this is equal to V.
    virtual bool isEqual(AbstractValue *V) = 0;
    /// Widen this by using V, and optionally a jump-set J.
    /// lessOrEqual(V) must return true.
    virtual void widening(AbstractValue *V, const std::vector<int64_t> &J) = 0;
    /// Pretty-printer of the abstract value.
    virtual void print(raw_ostream &Out) const{
      if (!isConstant()){
	if (var->hasName()) Out << var->getName() << "=" ;
      }
    }

    /// Return true if this is syntactically equal to V.
    virtual bool isIdentical(AbstractValue *V) = 0;

    // Specific transfer functions

    /// Execute an arithmetic operation in the abstract domain.
    virtual AbstractValue * visitArithBinaryOp(AbstractValue *, AbstractValue *,
					       unsigned, const char *) = 0;
    /// Execute a bitwise operation in the abstract domain.
    virtual AbstractValue * visitBitwiseBinaryOp(AbstractValue *, AbstractValue *, 
						 const Type *,const Type *, unsigned, const char *) = 0;
    /// Execute a casting operation in the abstract domain.
    virtual AbstractValue * visitCast(Instruction &, AbstractValue *, TBool*, bool) = 0;

    // Methods to evaluate a guard
    virtual bool comparisonSle(AbstractValue *) = 0;
    virtual bool comparisonSlt(AbstractValue *) = 0;
    virtual bool comparisonUle(AbstractValue *) = 0;
    virtual bool comparisonUlt(AbstractValue *) = 0;
    // Method to refine the abstract value using a conditional
    virtual void filterSigma(unsigned, AbstractValue*, AbstractValue*) = 0;
			     
  }; 
} // End llvm namespace

#endif
