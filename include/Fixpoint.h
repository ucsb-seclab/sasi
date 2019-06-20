// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __FIXPOINT_H__
#define __FIXPOINT_H__
//////////////////////////////////////////////////////////////////////////////
/// \file Fixpoint.h
///       Iterative Forward Abstract Interpreter 
//////////////////////////////////////////////////////////////////////////////
///
/// Representation of an abstract state.
///
/// Each block maintains its own map from variables to abstract
/// values (i.e., abstract state). The main reason for that is to
/// allow to modify abstract values of variables used in branch
/// conditions that may not be in SSA form. E.g.,
///
/// \verbatim
///   if (x>=5)
///    here we can refine x to [5,+oo]
///   else
///    here we can refine x to [-oo,4]
///   endif
/// \endverbatim
///
/// As a result, the fixpoint must ensure that all block maps are
/// consistent with each other. For efficiency reasons, whenever a
/// variable V changes its abstract value we update its users but
/// only in those blocks where the users live. The rest of blocks
/// which have also a copy of V will not be updated. This is correct
/// since those outdated values will not be used but we have to be
/// careful when we display results and filter those outdated
/// values. The use of live variable analysis would help a lot because
/// a block should not include in its map a variable is not
/// alive. This would save memory consumption. We do not currently use
/// live variable information.
///  
/// Notation
///
/// We call a "filter" just the constraint originated from a
/// conditional branch that can be used in a successor block to refine
/// the abstract value of the variables used in the constraint. In the
/// above example, we have two filters "x>=5" and "x<5".
/// 
/// \fixme: modifications to handle non-lattice abstract domains.
//////////////////////////////////////////////////////////////////////////////

#define DEBUG_TYPE "RangeAnalysis"
//#define WARNINGS //!< If we want to display warning messages

#include "AbstractValue.h"
#include "AbstractBlock.h"
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
#include "llvm/Analysis/Dominators.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Timer.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/DepthFirstIterator.h"

using namespace std;
using namespace llvm;

namespace unimelb {

  /// This class maps each BasicBlock to its set of defined Values
  /// (i.e., Values that appear on the lhs in the block's
  /// instructions).
  class Environment{
  public:
    /// Constructor of the class.
    Environment(Module *M){
      for (Module::iterator F = M->begin(), E=M->end() ; F != E; ++F){
	if (Utilities::IsTrackableFunction(F)){
	  for (Function::iterator B = F->begin(), EE = F->end(); B != EE; ++B){
	    SmallPtrSet<Value*, 32> vars;
	    env.insert(std::make_pair(B,vars));
	  }
	}
      }
    }
    /// Destructor of the class
    ~Environment(){}
    /// Add a variable into the environment associated with a basic block.
    void addVar(BasicBlock *BB, Value *V){
      unsigned Width;
      Type * Ty;
      bool IsTrackableType = Utilities::getTypeAndWidth(V, Ty, Width);
      if (IsTrackableType){
	DenseMap<BasicBlock*, SmallPtrSet<Value*, 32> >::iterator It = env.find(BB);
	assert(It != env.end());
	(*It).second.insert(V);
      }
    }
    void addVar(Value *V){
      unsigned Width;
      Type * Ty;
      bool IsTrackableType = Utilities::getTypeAndWidth(V, Ty, Width);
      if (IsTrackableType)
	flat_env.insert(V);
    }
    /// Return the environment of a basic block.
    SmallPtrSet<Value *, 32> getEnv(BasicBlock *BB){
      DenseMap<BasicBlock*, SmallPtrSet<Value*, 32> >::iterator It = env.find(BB);
      assert(It != env.end());
      return (*It).second;
    }
    std::set<Value *> getEnv(){ return flat_env; }
  private:
    DenseMap<BasicBlock*, SmallPtrSet<Value*, 32> > env; //!< the environment.   
    std::set<Value*>                           flat_env;            
  };

  /// This class computes a fixpoint of the program.
  class Fixpoint {    
  public:
    /// Constructors of the class
    Fixpoint(Module *M, unsigned WidenL, unsigned NarrowL, AliasAnalysis* AA);
    /// If isSigned is true then all integers will be considered as signed.
    Fixpoint(Module *M, unsigned WidenL, unsigned NarrowL, AliasAnalysis* AA, 
	     bool isSigned);
    /// Destructor of the class
    virtual ~Fixpoint();

    /// Methods for support type inquiry through isa, cast, and dyn_cast.
    static inline bool classof(const Fixpoint *) { return true; }

    /// Identify the variables to be tracked for the intraprocedural
    /// analysis.
    void init(Function *F, DominatorTree *); 
    /// Produce an intraprocedural global fixpoint.
    void solve(Function *F); 
    /// Output fixpoint results
    void printResultsGlobals(raw_ostream &);
    void printResultsFunction(Function *, raw_ostream &);
    void printResults(raw_ostream &);
    /// Gather some quick stats
    void gatherStats();

    /// Create a bottom abstract value from the underlying abstract
    /// domain.
    virtual AbstractValue* initAbsValBot(Value *) = 0;
    /// Create a top abstract value from the underlying abstract
    /// domain.
    virtual AbstractValue* initAbsValTop(Value *) = 0;
    // Create an abstract value from an integer constant from the
    // underlying abstract domain.
    virtual AbstractValue* initAbsIntConstant(ConstantInt *) = 0;
    /// Create an abstract value from a value initialized to an
    /// integer constant from the underlying abstract domain.
    virtual AbstractValue* initAbsValIntConstant(Value *, ConstantInt *) = 0;


    // Auxiliary methods

    /// Execute abstractly F.
    void solveLocal(Function *F);
    /// Compute a fixpoint until no change applying the corresponding
    /// transfer function. The fixpoint is demand-driven in the sense
    /// that it only recomputes affected instructions/blocks.
    void computeFixpo();
    /// Perform one fixpoint iteration without applying widening.
    void computeOneNarrowingIter(Function *);
    /// Call computeOneNarrowingIter NarrowL times.
    void computeNarrowing(Function *);
    
    /// Mark a block as executable.
    void markBlockExecutable(BasicBlock *);
    /// Mark an edge as executable.
    void markEdgeExecutable(BasicBlock *,BasicBlock *);
    /// Return true if the edge is feasible.
    bool isEdgeFeasible(BasicBlock *, BasicBlock *);


    /// Propagate the content of the predecessor map to the
    /// current block map. This is needed since each block keeps its
    /// own map from concrete to abstract values.
    void propagatePredecessors(BasicBlock*);     
    void generateFilters(BasicBlock *, BasicBlock *);
    void evalFilter(AbstractValue *&, const FiltersTy, const MapValToAbstractTy);

    void updateState(Instruction &, MapValToAbstractTy &, 
		     AbstractValue* Old, AbstractValue* New);
    void updateCondFlag(Instruction &, TBool *);

    void notifyUser(Value *, BasicBlock *, AbstractBlock *, Instruction* User);
    void keepConsistentMaps(BasicBlock * FromB, AbstractBlock *FromAbsB, 
			    BasicBlock * ToB  , AbstractBlock *ToAbsB,
			    Value *V);

    /// Execute an instruction I.
    void visitInst(Instruction &I);
    /// Execute a PHI instruction I.
    void visitPHINode(PHINode &I);
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
    /// Execute a boolean logical instruction (and/or/xor
    /// whose operands are of type i1).
    void visitBooleanLogicalInst(Instruction &I);

    ///  Mark the global variables of the module M.
    void addTrackedGlobalVariables(Module *M);
    void addTrackedGlobalVariablesPessimistically(Module *);
    ///  Mark the abstraction points of the function F.
    void addTrackedWideningPoints(Function *F);
    ///  Gather the integer constants that appear in the function F.
    void addTrackedIntegerConstants(Function * F);

    ///  Return true if widening must be applied.
    bool Widen(Instruction *,unsigned);

    ///  Make conservative assumptions when the code of a function
    ///  is not available or intraprocedural analysis.
    void FunctionWithoutCode(CallInst *, Function *, Instruction *);

    /// Succeed if the value is a Boolean flag which is being tracked.
    inline bool isTrackedCondFlag(Value *V){
      DenseMap<Value*,TBool*>::iterator I = TrackedCondFlags.find(V);
      return (I != TrackedCondFlags.end());
    }

    /// Succeed if the value is "true".
    inline bool isTrueConstant(Value *V){      
      if (V->getType()->isIntegerTy(1)){
	if (ConstantInt *C = dyn_cast<ConstantInt>(V)){	  
	  Constant * True = dyn_cast<Constant>(V);
	  return (True == C->getTrue(V->getType()->getContext()));
	}
      }
      return false;
    }
    
    /// Succeed if the value is "false".
    inline bool isFalseConstant(Value *V){      
      if (V->getType()->isIntegerTy(1)){
	if (ConstantInt *C = dyn_cast<ConstantInt>(V)){	  
	  Constant * True = dyn_cast<Constant>(V);
      return (True == C->getFalse(V->getType()->getContext()));
	}
      }
      return false;
    }
    
    /// Convert a Value into a TBool. Otherwise, return NULL.
    TBool* getTBoolfromValue(Value *V){
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
    
    void cleanupPreviousFunctionAnalysis(Function *);

  private:

    Module * M;     //!< The module where the analysis lives.
    DenseMap<Function*,DominatorTree*> DTs; //!<  Dominator trees for all functions.
    DominatorCacheTy  DTCache; //!< To reduce the number of dominance queries.

    /// Map blocks to abstract values.
    DenseMap<BasicBlock*, AbstractBlock*> BasicBlockToAbstractBlock;
    DenseMap<Value*,TBool*> TrackedCondFlags; //!< Map Values to Boolean flags.
    Environment *env; //!< Values tracked by each basic block.

    std::set<Value*>     InstWorkList; //!< Worklist of instructions to process.
    std::set<BasicBlock*>  BBWorkList; //!< Worklist of blocks to process.
    SmallPtrSet<BasicBlock*, 16>  BBExecutable; //!< Set of executable blocks.  
    typedef std::pair<BasicBlock*,BasicBlock*> Edge; //!< CFG edge.
    std::set<Edge>  KnownFeasibleEdges;  //!< Set of executable edges.

    /// Extra user chains that the analysis must keep track of. The
    /// analysis may modify some variables which are not in SSA
    /// form. Therefore, we need to keep its users for propagating changes.
    DenseMap<Value*, filter_users *> TrackedFilterUsers;     

    /// AA  - Alias Information used for global variables.
    AliasAnalysis * AA;
    
    /// For loops

    /// Set of widening points.
    SmallPtrSet<Instruction*,16> WideningPoints;
    /// If zero then widening is not applied.
    /// Of course, make sure that the abstract lattice
    /// is finite. Otherwise, we will not terminate.
    unsigned WideningLimit; 
    /// Set of integer constants that appear in the program. Used by
    /// jump-set widening.
    ConstantSetTy ConstSet; 
    /// Map a constant to its abstract value.
    DenseMap<Value*, AbstractValue*> ConstValMap;
    /// If NarrowingLimit zero then narrowing is not applied.
    unsigned NarrowingLimit;
    /// If true then k fixpoint iterations
    /// without widening are executed. The value of k is defined by
    /// NarrowingLimit
    bool NarrowingPass;


    /// For functions

    /// TrackedRecursiveFunctions - set of recursive functions
    SmallPtrSet<Function*, 16> TrackedRecursiveFunctions;
    /// Set of global variables that the analysis will try to keep
    /// track of.
    SmallPtrSet<GlobalVariable*, 64> TrackedGlobals;
    /// Map a global variable to its abstract value.
    DenseMap<Value*, AbstractValue*> GlobalValMap;

    /// Hook to consider all integers signed or unsigned in
    /// case the underlying abstract domain does not know what to do
    /// with signedeness.
    bool IsAllSigned;

    // For profiling
    // TimerGroup * TG;
    // Timer*T0; Timer*T1;    Timer*T2;    Timer*T3;    Timer*T4;    Timer*T5;
    // Timer*T6; Timer*T7;
    
    /// Lookup of V in all of the tracked maps.
    AbstractValue* 
    Lookup(MapValToAbstractTy ValMap, Value *V, bool ExceptionIfNotFound){
      AbstractValue* AbsVal=NULL;
      if (V->getValueID() != Value::UndefValueVal){
	if (TrackedGlobals.count(dyn_cast<GlobalVariable>(V)))
	  AbsVal = GlobalValMap.lookup(V);
	else if (ConstSet.count((dyn_cast<ConstantInt>(V))->getValue().getSExtValue()))
	  AbsVal = ConstValMap.lookup(V);
	else
	  AbsVal = ValMap.lookup(V);
      }
      assert(!ExceptionIfNotFound || AbsVal);
      return AbsVal;
    }
    /// Find the abstract block associated with V assuming V is an
    /// instruction. Otherwise, it raises an exception.
    AbstractBlock* FindMap(Value *V){
      Instruction *I = dyn_cast<Instruction>(V);
      assert(I);
      DenseMap<BasicBlock*, AbstractBlock*>::iterator 
	It = BasicBlockToAbstractBlock.find(I->getParent());
      assert(It != BasicBlockToAbstractBlock.end());      
      return It->second;		   
    }
  };

} // End llvm namespace

#endif
