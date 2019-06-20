// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __FIXPOINT_SSI_H__
#define __FIXPOINT_SSI_H__
//////////////////////////////////////////////////////////////////////////////
/// \file FixpointSSI.h
///       Iterative Forward Abstract Interpreter with SSI.
///
/// Representation of an abstract state.
///
/// For efficiency, the analysis maintains a unique map from variables
/// to abstract values. Therefore, the analysis can only
/// make claims about variables at the end of each function.
///
/// SSI (Static Single Information).
///
/// SSI form is an extension of SSA form that ensures that a
/// variable can be used only once through any path in the CFG. To do
/// that, SSI adds "sigma nodes" in addition to phi nodes. E.g., given
/// the following code:
///
/// \verbatim
///  if (x>=5)
///   y = x;
///  else
///   z = x;
///  endif
/// \endverbatim
///
/// Its SSI version is:
///
/// \verbatim
///  if (x>=5)
///   x.1 = sigma(x, if coming from then branch)
///  else
///   x.2 = sigma(x, if coming from else branch)
///  endif
///  x.3 = phi(x.1,x.2) 
/// \endverbatim
///
/// Note that SSI form redefines x in the then branch to x.1 and x.2
/// in the else. Since x.1 and x.2 are in SSA form then, it is
/// straightforward for the analysis to refine x.1 to [5,+oo] and x.2
/// to [-oo,4], respectively.
///
/// SSI is often used for backward analyses but rarely for forward
/// analyses. The reason is that strictly speaking we do not need SSI
/// form for forward analyses. Instead, we can associate each basic
/// block with its own map from variables to abstract values. Then,
/// whenever a branch condition is executed its successor can refine
/// the abstract values in its own copy and then propagate
/// changes to the other affected maps held by other basic blocks. 
/// 
/// We implemented this but it turned out that it is much slower that
/// the version using SSI.
///
/// Terminology
///
/// We call a "filter" just the constraint originated from a
/// conditional branch that can be used in a successor block to refine
/// the abstract value of the variables used in the constraint. In the
/// above example, we would have two filters "x>=5" and "x<5".
//////////////////////////////////////////////////////////////////////////////

#include "AbstractValue.h"
#include "Support/Utils.h"
#include "Support/TBool.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/Value.h"
#include "llvm/Constants.h"
#include "llvm/ValueSymbolTable.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include <tr1/memory>
#include <set>
#include <stack>

using namespace std;
using namespace llvm;

//#define WARNINGS //!< To display warning messages
#define DEBUG_TYPE "RangeAnalysis"
#define SKIP_TRAP_BLOCKS

namespace unimelb {

  /// Type that represents an abstract state.
  /// The fixpoint keeps a single map from Values to AbstractValues. 
  typedef DenseMap<Value*, AbstractValue*> AbstractStateTy;  
  typedef SmallPtrSet<Value*,8> SmallValueSet;
  /// Map from variable V to a set of sigma nodes S. V is a variable
  /// that appears in a conditional branch that was used to figure out
  /// the value of the each sigma node in S.
  typedef DenseMap<Value *, SmallValueSet *> SigmaUsersTy;         

  /// Class to represent a constraint.
  class BinaryConstraint{
  public:
    /// Constructor of the class.
    BinaryConstraint(unsigned _pred, Value* _Op1, Value* _Op2): 
      pred(_pred), Op1(_Op1), Op2(_Op2){}
    /// Destructor of the class.
    ~BinaryConstraint(){ }
    
    unsigned getPred(){ return pred;}
    unsigned getPred() const { return pred;}
    bool isConstantOperand(unsigned i){
      assert(i == 0 || i == 1);
      if (i==0) 
	return isa<ConstantInt>(Op1);
      else  
	return isa<ConstantInt>(Op2);
    }
    bool isEqual(BinaryConstraint *C){
      return ( (pred == C->getPred()) && (Op1 == C->getOperand(0)) && 
	       (Op2 == C->getOperand(1)));
    }
    Value*   getOperand(unsigned i){ 
      assert(i == 0 || i == 1);
      if (i==0) 
	return Op1;
      else 
	return Op2;
    }
    Value*   getOperand(unsigned i) const{ 
      assert(i == 0 || i == 1);
      if (i==0) 
	return Op1;
      else 
	return Op2;
    }
    
    void swap(){
      switch (pred) {
      default: assert(!"Unknown predicate!");
      case ICmpInst::ICMP_EQ:  pred = ICmpInst::ICMP_EQ;  break;
      case ICmpInst::ICMP_NE:  pred = ICmpInst::ICMP_NE;  break;
      case ICmpInst::ICMP_UGT: pred = ICmpInst::ICMP_ULT; break;
      case ICmpInst::ICMP_ULT: pred = ICmpInst::ICMP_UGT; break;
      case ICmpInst::ICMP_UGE: pred = ICmpInst::ICMP_ULE; break;
      case ICmpInst::ICMP_ULE: pred = ICmpInst::ICMP_UGE; break;
      case ICmpInst::ICMP_SGT: pred = ICmpInst::ICMP_SLT; break;
      case ICmpInst::ICMP_SLT: pred = ICmpInst::ICMP_SGT; break;
      case ICmpInst::ICMP_SGE: pred = ICmpInst::ICMP_SLE; break;
      case ICmpInst::ICMP_SLE: pred = ICmpInst::ICMP_SGE; break;
      }
      Value *Tmp = Op1;
      Op1=Op2;
      Op2=Tmp;
    }

    void print() const { 
      printOperand(Op1); printPred(); printOperand(Op2); 
    }
    
  private:
    unsigned pred;
    Value* Op1;
    Value* Op2;

    void printPred() const{
      switch (pred) {
      case ICmpInst::ICMP_EQ:  dbgs() << " = "   ; break;
      case ICmpInst::ICMP_NE:  dbgs() << " != "  ; break;
      case ICmpInst::ICMP_UGT: dbgs() << " u_> " ; break;
      case ICmpInst::ICMP_ULT: dbgs() << " u_< " ; break;
      case ICmpInst::ICMP_UGE: dbgs() << " u_>= "; break;
      case ICmpInst::ICMP_ULE: dbgs() << " u_=< "; break;
      case ICmpInst::ICMP_SGT: dbgs() << " s_> " ; break;
      case ICmpInst::ICMP_SLT: dbgs() << " s_< " ; break;
      case ICmpInst::ICMP_SGE: dbgs() << " s_>= "; break;
      case ICmpInst::ICMP_SLE: dbgs() << " s_=< "; break;
      }
    }

    void printOperand(Value *V) const{
      if (ConstantInt * C = dyn_cast<ConstantInt>(V)){
	unsigned width;
	Utilities::getIntegerWidth(V->getType(), width);
	// Boolean Constant
	if (width == 1){ // Boolean flag
	  if (ConstantInt::getTrue(V->getType()) == dyn_cast<Constant>(V))
	    dbgs() << "true";
	  else if (ConstantInt::getFalse(V->getType()) == dyn_cast<Constant>(V))
	    dbgs() << "false";
	  else{	  	    
	    switch(C->getSExtValue()){ // int64_t 
	    case 0: dbgs() << "false"; break;
	    case 1: dbgs() << "true";  break;
	    default: llvm_unreachable("Problems during printOperand");
	    }
	  }
	  return;
	}
	int64_t Val = C->getSExtValue();
	dbgs() << Val;
	return;
      }
      dbgs() << V->getName();
    }
  };
  typedef std::tr1::shared_ptr<BinaryConstraint>  BinaryConstraintPtr;
  struct BinaryConstraintCmp {
    bool operator()(const BinaryConstraintPtr C1, 
		    const BinaryConstraintPtr C2) const {
      // syntactic equivalence.
      return ( C1.get()->getPred()     == C2.get()->getPred() &&
      	       C1.get()->getOperand(0) == C2.get()->getOperand(0) &&
      	       C1.get()->getOperand(1) == C2.get()->getOperand(1));
    }
  };


  typedef DenseMap<Value* , BinaryConstraintPtr> SigmaFiltersTy;

  // This only used for widening
  enum OrderingTy { LESS_THAN, LEX_LESS_THAN };

  class FixpointSSI {    
  private:
    // To compute the fixpoint. 
    void solveLocal(Function *);
    void computeFixpo();
    // To perform narrowing.
    void computeNarrowing(Function *);
    void computeOneNarrowingIter(Function *);

    /// Record a block as executable.
    void markBlockExecutable(BasicBlock *);
    /// Record an CFG edge as feasible (i.e., executable).
    void markEdgeExecutable(BasicBlock *,BasicBlock *);
    /// Return true if the edge is feasible.
    bool isEdgeFeasible(BasicBlock *, BasicBlock *);
    /// Check if abstract value changed during last execution.
    void updateState(Instruction &, AbstractValue *);
    /// Check if Boolean flag changed during last execution.
    void updateCondFlag(Instruction &, TBool *);

    /// Execute an instruction I.
    void visitInst(Instruction &I);
    /// Execute a PHI instruction I if the domain is a lattice.
    void visitPHINode(PHINode &I);
    /// Execute a PHI instruction I if the domain is not a lattice.
    void visitPHINode(AbstractValue *&AbsVal, PHINode &I);
    /// Execute a Store instruction I.
    void visitStoreInst(StoreInst &I);
    /// Execute a Select instruction I
    void visitSelectInst(SelectInst &I);
    /// Execute a Load instruction I.
    void visitLoadInst(LoadInst &I);
    /// Execute a Return instruction I.
    void visitReturnInst(ReturnInst &I);
    /// Execute a Call instruction I.
    void visitCallInst(CallInst &I); 
    /// Execute a Terminator instruction I.
    void visitTerminatorInst(TerminatorInst &I);
    /// Execute a Comparison instruction I.
    void visitComparisonInst(ICmpInst &I);
    /// Execute a Sigma instruction
    void visitSigmaNode(AbstractValue *LHSSigma, Value * RHSSigma);
    void visitSigmaNode(AbstractValue *LHSSigma, Value * RHSSigma, 
			BasicBlock *, BranchInst * BI);

    void generateFilters(Value *, Value *, BranchInst *, BasicBlock *); 
    bool evalFilter(AbstractValue * &, Value *);
    // void generateFilters(Value *, Value *, BranchInst *, BasicBlock *, 
    // 			 FiltersTy &);
    // bool evalFilter(AbstractValue * &, Value *, const FiltersTy );
    /// Execute a Boolean logical instruction: and/or/xor whose
    /// operatons of i1.
    void visitBooleanLogicalInst(Instruction &I);

    ///  Mark the global variables of the module M.
    void addTrackedGlobalVariables(Module *M);
    void addTrackedGlobalVariablesPessimistically(Module *);
    ///  Mark the abstraction points of the function F.
    void addTrackedWideningPoints(Function *F);
    ///  Record the integer constants that appear in the function F.
    void addTrackedIntegerConstants(Function * F);
    void addTrackedValuesUsedSigmaNode(Value *,Value *); 
      
    /// Return true if widening must be applied.
    bool Widen(Instruction *,unsigned);

    /// Make conservative assumptions when the code of a function
    /// is not available or we do not want to analyze the function.
    void FunctionWithoutCode(CallInst *, Function *, Instruction *);

    /// Cleanup to make sure the analysis of a function does not
    /// interfere with other functions.
    inline void Cleanup(){
      ValueState.clear();
      TrackedCondFlags.clear();
      InstWorkList.clear();
      BBWorkList.clear();
      BBExecutable.clear();
      KnownFeasibleEdges.clear();
      WideningPoints.clear();
#ifdef SKIP_TRAP_BLOCKS
      TrackedTrapBlocks.clear();
#endif 
      ConstSet.clear();
    }
    
  public:    
    /// Constructors of the class
    FixpointSSI(Module *, unsigned WidL, unsigned NarL, AliasAnalysis*, 
		OrderingTy);
    FixpointSSI(Module *, unsigned WidL, unsigned NarL, AliasAnalysis*, bool isSigned, 
		OrderingTy);
		
    /// Destructor of the class
    virtual ~FixpointSSI();
    /// Methods for support type inquiry through isa, cast, and dyn_cast.
    static inline bool classof(const FixpointSSI *) { return true; }
   
    /// Identify the variables to be tracked for the analysis,
    /// and give them their corresponding initial abstract value.
    void init(Function *F); 
    /// Produce an intraprocedural fixpoint for F.
    void solve(Function *F);
    /// Output fixpoint results for the whole module.
    void printResults(raw_ostream &);
    void printResultsGlobals(raw_ostream &);
    void printResultsFunction(Function *, raw_ostream &);

    /// Create a bottom abstract value.
    virtual AbstractValue* initAbsValBot(Value *)=0;
    /// Create a top abstract value.
    virtual AbstractValue* initAbsValTop(Value *)=0;
    /// Create an abstract value from an integer constant.
    virtual AbstractValue* initAbsIntConstant(ConstantInt *)=0;
    /// Create an abstract value from a value initialized to an
    /// integer constant.
    virtual AbstractValue* initAbsValIntConstant(Value *,ConstantInt *)=0;

    /// To provide the analysis results to other passes.
    /// FIXME: not nice since we are returning internal information.
    inline AbstractStateTy getValMap() const { 
      return ValueState; 
    } 
    inline bool IsReachable(BasicBlock *B) const {
      return (BBExecutable.count(B) > 0);
    }

  private:
    Module * M;     //!< The module where the analysis lives.
    AbstractStateTy ValueState; //!< Map Values to abstract values.
    DenseMap<Value*,TBool*> TrackedCondFlags; //!< Map Values to Boolean flags.
    std::set<Value*> InstWorkList; //!< Worklist of instructions to process.
    std::set<BasicBlock*>  BBWorkList; //!< Worlist of blocks to process.
    SmallPtrSet<BasicBlock*, 16>  BBExecutable; //!< Set of executable blocks.  
    typedef std::pair<BasicBlock*,BasicBlock*> Edge; //!< CFG edge.
    std::set<Edge>  KnownFeasibleEdges;  //!< Set of executable edges.

    /// If a sigma node S depends on a comparison instruction that
    /// involves two variables X and Y, S will be user only of one of
    /// them. We use this map to remember that S is user of both X and
    /// Y.
    SigmaUsersTy TrackedValuesUsedSigmaNode;    
    SigmaFiltersTy SigmaFilters; 
   
    /// Set of widening points.
    SmallPtrSet<Instruction*,16> WideningPoints;
    /// If zero then widening will not be applied. Otherwise, it
    /// refers to the number of times an abstract value must change
    /// until we widen it. Once, we widen a value its counter starts
    /// from 0 again.
    unsigned WideningLimit; 
    /// Set of integer constants that appear in the program. Used by
    /// jump-set widening.
    std::vector<int64_t> ConstSet; 
    OrderingTy ConstSetOrder;
    /// If NarrowingLimit zero then narrowing will not be applied.
    unsigned NarrowingLimit;
    /// Internal flag for the analysis to know that it is performing
    /// narrowing.
    bool NarrowingPass;

    /// AA - Alias Information 
    AliasAnalysis * AA;

    /// Set of global variables that the analysis will keep track of.
    SmallPtrSet<GlobalVariable*, 64> TrackedGlobals;

    /// [HOOK] To consider all integers signed or not.
    bool IsAllSigned;

#ifdef SKIP_TRAP_BLOCKS
    DenseMap<BasicBlock*,unsigned int> TrackedTrapBlocks;
#endif 


    /// Return true if the instruction has a left-hand side.
    inline bool HasLeftHandSide(Instruction &I);
    /// Lookup in ValueState covering the special case if the value is
    /// undefined.
    AbstractValue* Lookup(Value *V,  bool ExceptionIfNotFound);
    /// Succeed if the value is a Boolean flag which is being tracked.
    inline bool isTrackedCondFlag(Value *V);
    /// Succeed if the value is "true".
    inline bool isTrueConstant(Value *V);
    /// Succeed if the value is "false".
    inline bool isFalseConstant(Value *V);
    /// Convert a Value into a TBool. Otherwise, return NULL.
    TBool* getTBoolfromValue(Value *V);
    /// Return true if Value is a Boolean flag.
    inline bool  isCondFlag(Value *V);
    /// Return true if the type of the instruction is
    /// of type 1-bit integer and its opcode is either And, Or, or Xor
    /// (i.e., Boolean flag).
    bool IsBooleanLogicalOperator(Instruction *I);
  };

  inline bool FixpointSSI::HasLeftHandSide(Instruction &I){
    if (I.isTerminator())    
      return false;
    if (I.isBinaryOp() || I.isCast()) 
      return true;
    if (isa<PHINode>(&I) || isa<ICmpInst>(&I) || isa<SelectInst>(&I) )    
      return true;   
    if (isa<CallInst>(&I))
      return (!I.getType()->isVoidTy());
    if (isa<LoadInst>(&I) || isa<AllocaInst>(&I) || isa<GetElementPtrInst>(&I))
      return true;
    ////////////////////////////////////////////////////////////////////
    // Otherwise:
    //
    // Store, GetElementPtr, GetElementPtrInst Fence, FenceInst,
    // AtomicCmpXchg , AtomicCmpXchgInst, AtomicRMW , AtomicRMWInst
    //
    // FCmp, VAArg, ExtractElement, InsertElement, ShuffleVector,
    // ExtractValue, InsertValue, LandingPad
    ////////////////////////////////////////////////////////////////////
    return false;
  }
  
  AbstractValue* FixpointSSI::Lookup(Value *V,  bool ExceptionIfNotFound){
    AbstractValue* AbsVal=NULL;
    if (V->getValueID() != Value::UndefValueVal)
      AbsVal = ValueState.lookup(V);
    
      assert(!ExceptionIfNotFound || AbsVal);      
      return AbsVal;
      
  }
  
  inline bool FixpointSSI::isTrackedCondFlag(Value *V){
    DenseMap<Value*,TBool*>::iterator I = TrackedCondFlags.find(V);
    return (I != TrackedCondFlags.end());
  }

  inline bool FixpointSSI::isTrueConstant(Value *V){      
    if (V->getType()->isIntegerTy(1)){
	if (ConstantInt *C = dyn_cast<ConstantInt>(V)){	  
	  Constant * True = dyn_cast<Constant>(V);
	  return (True == C->getTrue(V->getType()->getContext()));
	}
    }
    return false;
    }
  
  inline bool FixpointSSI::isFalseConstant(Value *V){      
    if (V->getType()->isIntegerTy(1)){
      if (ConstantInt *C = dyn_cast<ConstantInt>(V)){	  
	Constant * True = dyn_cast<Constant>(V);
	return (True == C->getFalse(V->getType()->getContext()));
      }
      }
    return false;
  }
  
  TBool* FixpointSSI::getTBoolfromValue(Value *V){
    if (isTrackedCondFlag(V))
      return TrackedCondFlags[V];      
    if (isTrueConstant(V)){
      TBool * c = new TBool();
      c->makeTrue();
      return c;
    }      
    if (isFalseConstant(V)){
      TBool * c = new TBool();
      c->makeFalse();
      return c;
    } 
    return NULL;      
  }

  inline bool  FixpointSSI::isCondFlag(Value *V){
    if (V->getType()->isIntegerTy(1))
      return true;   
    
    if (V->getType()->isPointerTy())
      return V->getType()->getContainedType(0)->isIntegerTy(1);
    
    return false;
  }
    
  
  bool FixpointSSI::IsBooleanLogicalOperator(Instruction *I){
    return (  I->getType()->isIntegerTy(1) && 
	      (I->getOpcode() == Instruction::And ||
	       I->getOpcode() == Instruction::Or ||
	       I->getOpcode() == Instruction::Xor ) ) ;
  }
    

} // End llvm namespace

#endif
