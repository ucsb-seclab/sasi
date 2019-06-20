// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file RangeVariableAnalyses.cpp
///       Range Integer Variable Passes.
//////////////////////////////////////////////////////////////////////////////

#include "FixpointSSI.h"
#include "Transformations/vSSA.h"
#include "Range.h"
#include "WrappedRange.h"
#include "StridedWrappedRange.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Module.h"
#include "llvm/Value.h"
#include "llvm/Instructions.h"
#include "llvm/ValueSymbolTable.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include <llvm/Analysis/Trace.h>
#include <llvm/Analysis/DebugInfo.h>
#include <time.h>
#include "ArrayIndexManager.h"

using namespace llvm;
using namespace unimelb;
using namespace NEWEVAL;


cl::opt<unsigned>  
widening("widening",
	 cl::init(3),
	 cl::Hidden,
	 //!< User option to choose widening threshold.
	 cl::desc("Widening threshold (0: no widening)")); 

cl::opt<unsigned>  
narrowing("narrowing",
	  cl::init(1),
	  cl::Hidden,
	  //!< User option to choose narrowing.
	  cl::desc("Narrowing iterations (0: no narrowing)")); 

cl::opt<bool> 
enableOptimizations("enable-optimizations", 
		    cl::Hidden,
		    cl::desc("Enable LLVM optimizations (default = false)"),
		    //!< User option to run LLVM optimizations.
		    cl::init(false)); 

cl::opt<bool> 
instCombine("InstCombine", 
	    cl::Hidden,
	    cl::desc("Enable -instcombine LLVM pass (default = false)"),
	    //!< User option to run -instcombine.
	    cl::init(false)); 

cl::opt<unsigned> 
Inline("Inline", 
       cl::init(0),
       cl::Hidden,
       //!< User option to inline functions.
       cl::desc("Enable inlining of functions (default = 0)")); 

cl::opt<string> 
runOnlyFunction("only-function", 
		cl::desc("Specify function name"), 
		cl::value_desc(""));

cl::opt<int> 
numFuncs("numfuncs", 
       cl::init(-1),
       cl::Hidden,
       cl::desc("Number of functions to be analyzed (default = -1, all)")); 

// For range analysis
#define SIGNED_RANGE_ANALYSIS true
// For verbose mode
// #define VERBOSE
// Count a difference if the precision improvement is strictly greater
// than K. The value of K should be defined in terms of cardinality of
// the result of gamma function.
#define PRECISION_TOLERANCE 0
// For printing analysis results
#define PRINT_RESULTS

namespace unimelb {

  /// An utility function that adds a pass to the pass manager.
  inline void addPass(PassManager &PM, Pass *P) {
    // Add the pass to the pass manager...
    PM.add(P);  
#ifdef VERBOSE
    dbgs() << "[RangeAnalysis]: running pass " <<  P->getPassName() << "\n";
#endif 
  }
  
  /// Add all LLVM passes into the pass manager.
  inline void addTransformPasses(PassManager &PM) {
    // We perform LCSSA pass before CFGSimplification to avoid doing
    // some code hoisting (HoistThenElseCodeToIf in
    // Transforms/Utils/SimplifyCFG). 
    //
    // Some code hoisting can make us losing precision if
    // simplifications like the following are performed:
    // bb8:
    //   ...
    //   %tmp11 = icmp ne i32 %tmp10, %x
    //   br i1 %tmp11, label %bb13, label %bb15
    // bb13:
    //   %tmp14 = add nsw i32 %i.0, 1
    //   br label %bb8
    // bb15:
    //   %tmp16 = add nsw i32 %i.0, 1
    //   ...
    // 
    // into:
    //
    // bb8: 
    //   ...
    //   %tmp11 = icmp ne i32 %tmp10, %x
    //   %tmp14 = add nsw i32 %i.0, 1
    //   br i1 %tmp11, label %bb8, label %bb15
    // 
    // The analysis rely on being able to filter the value of %i.0 in
    // bb13 using the branch conditional of bb8. If we allow merging
    // then we don't filter the value losing precision.

    if (instCombine){
      // This pass is useful among other things to remove casting
      // operations that may preclude us of refining using branch
      // conditions (e.g., t5-a.c)
      addPass(PM, createInstructionCombiningPass()); // remove redundancies
    }
    
    if (enableOptimizations){
      
      addPass(PM, createLoopSimplifyPass());        // Canonicalize natural loops 
      // addPass(PM, createLoopRotatePass());        
      addPass(PM, createLCSSAPass());               // Loop closed ssa form 
      addPass(PM, createCFGSimplificationPass());   // Clean up

      addPass(PM, createPromoteMemoryToRegisterPass());// Kill useless allocas
      addPass(PM, createDeadArgEliminationPass());   // Dead argument elimination
      addPass(PM, createGlobalDCEPass());            // Remove unused fns and globs
      addPass(PM, createGlobalOptimizerPass());      // optimizes non-address taken internal globals.
      addPass(PM, createCFGSimplificationPass());    // Clean up disgusting code

      addPass(PM, createSCCPPass());                  // Constant prop with SCCP
      addPass(PM, createIPConstantPropagationPass()); // IP Constant Propagation
      addPass(PM, createGVNPass());                   // Remove redundancies (e.g., load)
                                                      // it may introduce PHI nodes!
      addPass(PM, createDeadCodeEliminationPass());   // DCE
      addPass(PM, createAggressiveDCEPass());         // Delete dead instructions
      addPass(PM, createCFGSimplificationPass());     // Clean up after DCE  

      // if (Inline > 0){
      // 	// This pass is useful for obviuos reason but expensive.
      // 	addPass(PM, createFunctionInliningPass(Inline)); // Inline functions
      // 	addPass(PM, createCFGSimplificationPass());      // Clean up after DCE  
      // }

      addPass(PM, createUnifyFunctionExitNodesPass()); // at most one return
      addPass(PM, createCFGSimplificationPass());   // Another clean up
      addPass(PM, createLowerSwitchPass());         // Eliminate switch constructions  
      
    }
    else{
      addPass(PM, createUnifyFunctionExitNodesPass()); // at most one return
      addPass(PM, createLowerSwitchPass());            // Eliminate switch constructions  
    }

    if (instCombine){
      // This pass is useful among other things to remove casting
      // operations that may preclude us of refining using branch
      // conditions (e.g., t5-a.c)
      addPass(PM, createInstructionCombiningPass()); // remove redundancies
    }

    if (Inline > 0){
      // This pass is useful for obviuos reason but expensive.
      addPass(PM, createFunctionInliningPass(Inline)); // Inline functions
      //addPass(PM, createCFGSimplificationPass());      // Clean up after DCE  
    }

    addPass(PM, createvSSAPass());                     // Run vssa pass
  }

  /// To run all the transformations previous to the range analysis.
  struct RangeTransformationPass : public ModulePass{
    static char ID; //!< Pass identification, replacement for typeid    
    RangeTransformationPass() : ModulePass(ID) {}
    virtual bool runOnModule(Module &M){

      PassManager Passes;
      addTransformPasses(Passes);  
      Passes.run(M);

      return true;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
    }    
  };

  char RangeTransformationPass::ID = 0;
  static RegisterPass<RangeTransformationPass> YY("range-transformations",
						  "UNIMELB program transformations",
						  false, false);


  /// Classical fixed-width range analysis
  class RangeAnalysis: public FixpointSSI {
  private:
    bool IsSigned;
  public:
    RangeAnalysis(Module *M, 
		  unsigned WL, unsigned NL, 
		  AliasAnalysis *AA,  bool isSigned): 
      FixpointSSI(M,WL,NL,AA,isSigned,LESS_THAN), 
      IsSigned(isSigned){
    }

    // Methods that allows Fixpoint creates Range objects
    virtual AbstractValue* initAbsValBot(Value *V){
      Range * R = new Range(V,IsSigned);
      R->makeBot();
      return R;
    }
    virtual AbstractValue* initAbsValTop(Value *V){
      Range * R = new Range(V,IsSigned);
      return R;
    }
    virtual AbstractValue* initAbsIntConstant(ConstantInt *C){
      Range * R = new Range(C, C->getBitWidth(),IsSigned);
      return R;
    }
    virtual AbstractValue* initAbsValIntConstant(Value *V, ConstantInt *C){
      Range * RV = new Range(V,IsSigned);
      Range RC(C, C->getBitWidth(), IsSigned);
      RV->makeBot();
      RV->join(&RC);      
      return RV;
    }
  };


  /// Wrapped Interval Analysis
  class StridedWrappedRangeAnalysis: public FixpointSSI {
  public:
    StridedWrappedRangeAnalysis(Module *M, 
			 unsigned WL, unsigned NL, 
			 AliasAnalysis *AA): 
      FixpointSSI(M,WL,NL,AA,LEX_LESS_THAN){}

    // Methods that allows Fixpoint creates Range objects
    virtual AbstractValue* initAbsValBot(Value *V){
      StridedWrappedRange * R = new StridedWrappedRange(V);
      R->makeBot();
      return R;
    }
    virtual AbstractValue* initAbsValTop(Value *V){
      StridedWrappedRange * R = new StridedWrappedRange(V);
      return R;
    }
    virtual AbstractValue* initAbsIntConstant(ConstantInt *C){
      StridedWrappedRange * R = new StridedWrappedRange(C, C->getBitWidth());
      return R;
    }
    virtual AbstractValue* initAbsValIntConstant(Value *V, ConstantInt *C){
      StridedWrappedRange * RV = new StridedWrappedRange(V);
      StridedWrappedRange RC(C, C->getBitWidth());
      assert(RV);
      RV->makeBot();
      RV->join(&RC);      
      return RV;
    }
  };
  
  class WrappedRangeAnalysis: public FixpointSSI {
  public:
    WrappedRangeAnalysis(Module *M, 
			 unsigned WL, unsigned NL, 
			 AliasAnalysis *AA): 
      FixpointSSI(M,WL,NL,AA,LEX_LESS_THAN){}

    // Methods that allows Fixpoint creates Range objects
    virtual AbstractValue* initAbsValBot(Value *V){
      WrappedRange * R = new WrappedRange(V);
      R->makeBot();
      return R;
    }
    virtual AbstractValue* initAbsValTop(Value *V){
      WrappedRange * R = new WrappedRange(V);
      return R;
    }
    virtual AbstractValue* initAbsIntConstant(ConstantInt *C){
      WrappedRange * R = new WrappedRange(C, C->getBitWidth());
      return R;
    }
    virtual AbstractValue* initAbsValIntConstant(Value *V, ConstantInt *C){
      WrappedRange * RV = new WrappedRange(V);
      WrappedRange RC(C, C->getBitWidth());
      assert(RV);
      RV->makeBot();
      RV->join(&RC);      
      return RV;
    }
  };


  /// Return true if the analysis will consider F.
  bool IsAnalyzable(const Function *F, CallGraph &CG){
      // The numbers reported in the APLAS paper were obtained by
      // ignoring functions which were not called by "main".
      if (!Utilities::IsTrackableFunction(F)) return false;
      if (F->getName() == "main") return true;
      if (CallGraphNode * CG_F = CG[F]){
	if (CG_F->getNumReferences() == 1){
	  // The function is either unreachablle, external, or inlined.
	  return false;
	}
      }
      return true;
  }

  /// Common analyses needed by the range analysis.
  inline void RangePassRequirements(AnalysisUsage& AU){
    AU.addRequired<AliasAnalysis>();
    AU.addRequired<DominatorTree>();
    AU.addRequired<CallGraph>();
    AU.setPreservesAll(); // Does not transform code
  }    

  template<typename Analysis>
  void runAnalysis(Module &M, CallGraph *CG, Analysis a){
    if (runOnlyFunction != ""){
      Function *F = M.getFunction(runOnlyFunction); 
      if (!F){ 
	dbgs() << "ERROR: function " << runOnlyFunction << " not found\n\n";
	return;
      }
      a.init(F);
      a.solve(F);
#ifdef  PRINT_RESULTS 	  
      a.printResultsFunction(F,dbgs());
#endif 
    }
      else{
	int k=0;
	for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F){	  
	  if (IsAnalyzable(F,*CG)){
	    if ( (numFuncs > 0) && (k > numFuncs)) 
	      break;

	    DEBUG(dbgs() << "------------------------------------------------------------------------\n");
	    a.init(F);
	    a.solve(F);
#ifdef  PRINT_RESULTS 	  
	    //a.printResultsGlobals(dbgs());
	    a.printResultsFunction(F,dbgs());
#endif 
	    k++;
	  }
	}
      }
  }

  /// To run an intraprocedural range analysis.
  struct RangePass : public ModulePass{
    static char ID; //!< Pass identification, replacement for typeid    
    RangePass() : ModulePass(ID) {}
    virtual bool runOnModule(Module &M){

      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();
      
      dbgs() <<"\n===-------------------------------------------------------------------------===\n" ;  
      dbgs() << "               Range Integer Variable Analysis \n";
      dbgs() <<"===-------------------------------------------------------------------------===\n" ;      
      RangeAnalysis a(&M, widening , narrowing , AA, SIGNED_RANGE_ANALYSIS);
      runAnalysis(M,CG,a);
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  };


  /// To run an intraprocedural wrapped range analysis.
  struct WrappedRangePass : public ModulePass{
    static char ID; //!< Pass identification, replacement for typeid    
    WrappedRangePass() : ModulePass(ID) {}
    virtual bool runOnModule(Module &M){

      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();

      dbgs() <<"\n===-------------------------------------------------------------------------===\n";  
      dbgs() << "               Wrapped Range Integer Variable Analysis \n";
      dbgs() <<"===-------------------------------------------------------------------------===\n";      
      WrappedRangeAnalysis a(&M, widening , narrowing , AA);
      runAnalysis(M,CG,a);
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  };
  
  struct StridedWrappedRangePass : public ModulePass{
    static char ID; //!< Pass identification, replacement for typeid    
    StridedWrappedRangePass() : ModulePass(ID) {}
    virtual bool runOnModule(Module &M){

      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();

      dbgs() <<"\n===-------------------------------------------------------------------------===\n";  
      dbgs() << "               Strided Wrapped Range Integer Variable Analysis \n";
      dbgs() <<"===-------------------------------------------------------------------------===\n";      
      StridedWrappedRangeAnalysis a(&M, widening , narrowing , AA);
      runAnalysis(M,CG,a);
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  };


  char RangePass::ID = 0;
  static RegisterPass<RangePass> RP("range-analysis",
				    "Fixed-Width Integer Range Analysis",
				    false,false);

  char WrappedRangePass::ID = 0;
  static RegisterPass<WrappedRangePass> WRP("wrapped-range-analysis",
					    "Fixed-Width Wrapped Integer Range Analysis",
					    false,false);

  char StridedWrappedRangePass::ID = 0;
  static RegisterPass<StridedWrappedRangePass> SWRP("strided-wrapped-range-analysis",
					    "Strided Fixed-Width Wrapped Integer Range Analysis",
					    false,false);

  ////////////////////////////////////////////////////////////////////
  ///               PASSES FOR PAPER EXPERIMENTS
  ////////////////////////////////////////////////////////////////////

  /// This class runs -range-analysis and -wrapped-range-analysis
  /// passes and gather some numbers regarding precision.
  class runPrecComparison : public ModulePass{
  public:
    // Pass identification, replacement for typeid    
    static char ID; 
    /// Constructor of the class.
    runPrecComparison() :  ModulePass(ID), IsAllSigned(SIGNED_RANGE_ANALYSIS),       
			   NumTotal(0), NumOfSame(0), NumOfDifferent(0), 
			   NumUnWrappedIsBetter(0), NumWrappedIsBetter1(0), 
			   NumWrappedIsBetter2(0), 
			   NumOfIncomparable(0), NumOfTrivial(0){ }
    /// Destructor of the class.
    ~runPrecComparison(){}

    virtual bool runOnModule(Module &M){
     
      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();

      RangeAnalysis Unwrapped(&M, widening, narrowing, AA, SIGNED_RANGE_ANALYSIS);
      WrappedRangeAnalysis Wrapped(&M, widening, narrowing,  AA);
      if (runOnlyFunction != ""){
	Function *F = M.getFunction(runOnlyFunction); 
	if (!F){
	  dbgs() << "ERROR: function " << runOnlyFunction << " not found\n\n";
	  return false;
	}
	else
	  runAnalyses(Unwrapped, "Range Analysis", 
		      Wrapped  , "Wrapped Range Analysis", F);
      }
      else{
	int k =0;
	for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F){	  
	  if (IsAnalyzable(F,*CG)){
	    if ( (numFuncs > 0) && (k > numFuncs)) 
	      break;
	    Unwrapped.init(F);
	    Unwrapped.solve(F);
	    Wrapped.init(F);
	    Wrapped.solve(F);
	    compareAnalysesOfFunction(Unwrapped,Wrapped);
	    k++;
	  }
	} // end for
      }
      printStats(dbgs());     
      return false;
    }
    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  private:
    bool IsAllSigned;
   
    // Counters
    unsigned NumTotal;
    unsigned NumOfSame;
    unsigned NumOfDifferent;
    unsigned NumUnWrappedIsBetter;
    unsigned NumWrappedIsBetter1; // because unwrapped was top
    unsigned NumWrappedIsBetter2; // neither was top and wrapped is more precise.
    unsigned NumOfIncomparable;
    unsigned NumOfTrivial;
    
    template<typename Analysis1, typename Analysis2>
    void runAnalyses(Analysis1 a1, std::string a1_StrName,
		     Analysis2 a2, std::string a2_StrName, Function *F){

#ifdef  VERBOSE
	dbgs() << "---------------- Function " << F->getName() << "---------------------\n";
#endif 

#ifdef  VERBOSE
	dbgs() << "=== running  " << a1_StrName   << " ... ===\n";
#endif 
	a1.init(F);
	a1.solve(F);

#ifdef  VERBOSE
	dbgs() << "=== running  " << a2_StrName   << " ... ===\n";
#endif
	a2.init(F);
	a2.solve(F);

	compareAnalysesOfFunction(a1, a2);
    }

    void compareAnalysesOfFunction(const RangeAnalysis &Unwrapped,
				   const WrappedRangeAnalysis &Wrapped){

      // We cannot assume a particular order of the entries since LLVM
      // can generate different orders
      AbstractStateTy UnwrappedMap         = Unwrapped.getValMap();
      AbstractStateTy WrappedMap  = Wrapped.getValMap();     
      // This is expensive because is n*m where n,m sizes of the two
      // hash tables. Most of the time, n is equal to m.
      typedef AbstractStateTy::iterator It;
      for (It B=UnwrappedMap.begin(), E=UnwrappedMap.end(); B != E; ++B){
	if (!B->second){
	  continue;
	}
	if (Range * I1 = dyn_cast<Range>(B->second)){
	  if (I1 && (!I1->isConstant())){
	    AbstractValue *AbsVal =WrappedMap[B->first];
	    assert(AbsVal);
	    WrappedRange *I2 = dyn_cast<WrappedRange>(AbsVal);
	    assert(I2);
	    assert(!I2->isConstant());
	    compareTwoIntervals(I1,I2, IsAllSigned); 
	  }
	}
      } // end for
    }

    void compareTwoIntervals(Range *I1, WrappedRange* I2, bool isSigned){
      assert(I1); assert(I1->getWidth() == I2->getWidth());
      assert(I2); assert(I1->getValue() == I2->getValue());
      
      I1->normalize();
      I2->normalize();
      NumTotal++;

      if (I1->IsTop() && I2->IsTop()){
	NumOfTrivial++;
	return;
      }

      if (I1->isBot() || I2->isBot()){
	NumOfTrivial++;
	return;
      }
            
      uint64_t val_I1 = I1->Cardinality();
      uint64_t val_I2 = I2->Cardinality();
      uint64_t diff;
      if (val_I1 > val_I2)
	diff = val_I1 - val_I2;
      else
	diff = val_I2 - val_I1;

      if (diff <= PRECISION_TOLERANCE){
      	NumOfSame++;
      	return;
      }

      if (I1->IsTop() && !I2->IsTop()){
#ifdef VERBOSE
	dbgs() << "Wrapped more precise: ";
	I2->print(dbgs());
	dbgs() << " < ";
	I1->print(dbgs());
	dbgs() << "\n";
#endif 
	NumWrappedIsBetter1++;
	return;
      }

      if (!I1->IsTop() && I2->IsTop()){
#ifdef VERBOSE
	dbgs() << "Classical more precise: ";
	I1->print(dbgs());
	dbgs() << " < ";
	I2->print(dbgs());
	dbgs() << "\n";
#endif 
	NumUnWrappedIsBetter++;
	return;
      }

      APInt a = I1->getLB();
      APInt b = I1->getUB();
      WrappedRange NewI1(a,b,a.getBitWidth());
      if (I1->isBot()) NewI1.makeBot();
      if (I1->IsTop()) NewI1.makeTop();
      if (I2->isEqual(&NewI1)) {
	NumOfSame++;
	return;
      }

      if ( (I2->lessOrEqual(&NewI1))){
	if (NewI1.lessOrEqual(I2))
	  NumOfSame++;
	else{
#ifdef VERBOSE
	  dbgs() << "Wrapped more precise: ";
	  I2->print(dbgs());
	  dbgs() << " < ";
	  NewI1.print(dbgs());
	  dbgs() << "\n";
#endif 
	  NumWrappedIsBetter2++;
	}
      }
      else{
	if (NewI1.lessOrEqual(I2)){
#ifdef VERBOSE
	  dbgs() << "Classical more precise: ";
	  NewI1.print(dbgs());
	  dbgs() << " < ";
	  I2->print(dbgs());
	  dbgs() << "\n";
#endif 
	  NumUnWrappedIsBetter++;
	}
	else
	  NumOfIncomparable++;
      }      
    } // end function

    void printStats(raw_ostream &Out){
      Out << "=----------------------------------------------------------------------=\n";
      Out << "                         Summary results                                \n";
      Out << "=----------------------------------------------------------------------=\n";
      Out << "# tracked intervals                         : "  
	  <<  NumTotal  << "\n";
      Out << "# proper unwrapped intervals                : "  
	  <<  NumTotal - NumOfTrivial - NumWrappedIsBetter1 << "\n";
      Out << "# proper wrapped intervals                  : "  
	  <<  NumTotal - NumOfTrivial << "\n";
      Out << "# wrapped < unwrapped                       : " 
	  <<  NumWrappedIsBetter1+NumWrappedIsBetter2 
	  << " (tolerance=" <<  PRECISION_TOLERANCE << ")\n";
      // Out << "# proper intervals                          : "  
      // 	  <<  NumTotal - NumOfTrivial << "\n";
      // Out << "# wrapped == unwrapped                      : " 
      // 	  <<  NumOfSame << " (tolerance=" <<  PRECISION_TOLERANCE << ")\n";
      // Out << "# wrapped < unwrapped (unwrappred=[-oo,oo]) : "  
      // 	  <<  NumWrappedIsBetter1   << "\n";     
      // Out << "# wrapped < unwrapped (unwrappred!=[-oo,oo]): "  
      // 	  <<  NumWrappedIsBetter2   << "\n";     
      Out << "# unwrapped < wrapped                       : "  
	  <<  NumUnWrappedIsBetter << "    // should be 0. \n";
      Out << "=----------------------------------------------------------------------=\n";

    }
   
  }; // end of class runPrecComparison



 /// This class runs -range-analysis and -wrapped-range-analysis
  /// passes and gather some numbers regarding precision.
  class runBintComparison : public ModulePass{
  public:
    // Pass identification, replacement for typeid    
    static char ID; 
    /// Constructor of the class.
    runBintComparison() :  ModulePass(ID), IsAllSigned(SIGNED_RANGE_ANALYSIS),       
			   NumTotal(0), NumOfSame(0), NumOfDifferent(0), 
			   NumUnWrappedIsBetter(0), NumWrappedIsBetter1(0), 
			   NumWrappedIsBetter2(0), 
			   NumOfIncomparable(0), NumOfTrivial(0), 
         numberWrappedImpropedAlias(0), 
         numberStridedImprovedAlias(0) { }
    /// Destructor of the class.
    ~runBintComparison(){}

    virtual bool runOnModule(Module &M){
     
      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();


      WrappedRangeAnalysis Wrapped(&M, widening, narrowing,  AA);
      StridedWrappedRangeAnalysis strWrapped(&M, widening, narrowing,  AA);
      if (runOnlyFunction != ""){
	Function *F = M.getFunction(runOnlyFunction); 
	if (!F){
	  dbgs() << "ERROR: function " << runOnlyFunction << " not found\n\n";
	  return false;
	}
	else
	  runAnalyses(Wrapped  , "Wrapped Range Analysis", 
                 strWrapped, "Strided Wrapped Range Analysis", 
                 F);
      }
      else{
	int k =0;
	double strided_time = 0.0;
	double wrapped_time = 0.0;
	for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F){	  
	  if (IsAnalyzable(F,*CG)){
	    if ( (numFuncs > 0) && (k > numFuncs)) 
	      break;
	    clock_t t;
        t = clock();
	    strWrapped.init(F);
	    strWrapped.solve(F);
	    t = clock() - t;
	
    	double time_taken = ((double)t)/CLOCKS_PER_SEC;
    	strided_time += time_taken;
	    
	    clock_t t1;
        t1 = clock();
	    Wrapped.init(F);
	    Wrapped.solve(F);
	    t1 = clock() - t1;
    	time_taken = ((double)t1)/CLOCKS_PER_SEC;
    	wrapped_time += time_taken;
	    
	    compareAnalysesOfFunction(Wrapped, strWrapped);
	    k++;
	  }
	} // end for
	    dbgs() <<"Time:Strided"<< "=" << strided_time << "\n";
	    dbgs() <<"Time:Wrapped"<< "=" << wrapped_time << "\n";
      }
      printStats(dbgs());     
      return false;
    }
    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }    
  private:
    bool IsAllSigned;
   
    // Counters
    unsigned NumTotal;
    unsigned NumOfSame;
    unsigned NumOfDifferent;
    unsigned NumUnWrappedIsBetter;
    unsigned NumWrappedIsBetter1; // because unwrapped was top
    unsigned NumWrappedIsBetter2; // neither was top and wrapped is more precise.
    unsigned NumOfIncomparable;
    unsigned NumOfTrivial;
    unsigned numberStridedImprovedAlias;
    unsigned numberWrappedImpropedAlias;
    
    template<typename Analysis1, typename Analysis2>
    void runAnalyses(Analysis1 a1, std::string a1_StrName,
		     Analysis2 a2, std::string a2_StrName, Function *F){

#ifdef  VERBOSE
	dbgs() << "---------------- Function " << F->getName() << "---------------------\n";
#endif 

#ifdef  VERBOSE
	dbgs() << "=== running  " << a1_StrName   << " ... ===\n";
#endif 
    
	a1.init(F);
	a1.solve(F);
	

#ifdef  VERBOSE
	dbgs() << "=== running  " << a2_StrName   << " ... ===\n";
#endif
    
	a2.init(F);
	a2.solve(F);
	

	compareAnalysesOfFunction(a1, a2);

      computeAliasAnalysisImprovePercentage(a1, a2, F);
    }

    void compareAnalysesOfFunction(const WrappedRangeAnalysis &Wrapped, const StridedWrappedRangeAnalysis &strWrapped) {

      // We cannot assume a particular order of the entries since LLVM
      // can generate different orders
      AbstractStateTy strWrappedMap         = strWrapped.getValMap();
      AbstractStateTy WrappedMap  = Wrapped.getValMap();     
      // This is expensive because is n*m where n,m sizes of the two
      // hash tables. Most of the time, n is equal to m.
      typedef AbstractStateTy::iterator It;
      for (It B=WrappedMap.begin(), E=WrappedMap.end(); B != E; ++B){
        if (!B->second){
          continue;
        }
        if (WrappedRange * I1 = dyn_cast<WrappedRange>(B->second)){
          if (I1 && (!I1->isConstant())){
            AbstractValue *AbsVal =strWrappedMap[B->first];
            assert(AbsVal);
            StridedWrappedRange *I2 = dyn_cast<StridedWrappedRange>(AbsVal);
            assert(I2);
            /*if(I2->isConstant()) {
                I1->printRange(dbgs());
                I2->printRange(dbgs());
            }*/
            assert(!I2->isConstant());
            compareTwoIntervals(I1,I2, IsAllSigned); 
          }
        }
      } // end for

    }

    void computeAliasAnalysisImprovePercentage(const WrappedRangeAnalysis &Wrapped, const StridedWrappedRangeAnalysis &strWrapped, Function *targetFunc) {
      AbstractStateTy strWrappedMap = strWrapped.getValMap();
      AbstractStateTy WrappedMap = Wrapped.getValMap();     
      
      AllFuncValueGrTy& allFuncValues = ArrayIndexClassifier::getAllFuncValueGroup();

      std::map<const Value*, std::set<const Value *> > wrappedValueGroups;
      std::map<const Value*, std::set<const Value *> > stridedValueGroups;

      if(allFuncValues.find(targetFunc) == allFuncValues.end()) {
        return;
      }
        for(std::pair<const Value*, std::set<const Value*> > &currMap2: allFuncValues[targetFunc]) {
          wrappedValueGroups.clear();
          stridedValueGroups.clear();

          std::set<const Value*> totalValues;
          totalValues.clear();

          const std::set<const Value *> &checkVals = currMap2.second;
          for(const Value* currChkVal: checkVals) {
            Value* nonConstVal = const_cast<Value*>(currChkVal);
            if(WrappedMap.find(nonConstVal) != WrappedMap.end() && 
               strWrappedMap.find(nonConstVal) != strWrappedMap.end()) {
                totalValues.insert(nonConstVal);
            } else {
              continue;
            }

            wrappedValueGroups[currChkVal].insert(currChkVal);
            WrappedRange * I1 = dyn_cast<WrappedRange>(WrappedMap[nonConstVal]);

            for(std::pair<const Value*, std::set<const Value*> > &knownValGroup: wrappedValueGroups) {
              const Value* knownVal = knownValGroup.first;
              Value* nonConstKnownVal = const_cast<Value*>(knownVal);
              WrappedRange * knownRange = dyn_cast<WrappedRange>(WrappedMap[nonConstKnownVal]);
              if(knownRange->WrappedlessOrEqual((AbstractValue*)I1) && I1->WrappedlessOrEqual((AbstractValue*)knownRange)) {
                // not equal?
                knownValGroup.second.insert(currChkVal);
              } else {              
                WrappedRange meetRes = WrappedMeet(knownRange, I1);
                // intersection.
                if(!meetRes.isBot()) {
                  knownValGroup.second.insert(currChkVal);
                }
              }
            }

            stridedValueGroups[currChkVal].insert(currChkVal);
            StridedWrappedRange *I2 = dyn_cast<StridedWrappedRange>(strWrappedMap[nonConstVal]);
            for(std::pair<const Value*, std::set<const Value*> > &knownValGroup: stridedValueGroups) {
              const Value* knownVal = knownValGroup.first;
              Value* nonConstKnownVal = const_cast<Value*>(knownVal);
              StridedWrappedRange * knownRange = dyn_cast<StridedWrappedRange>(strWrappedMap[nonConstKnownVal]);

              if(knownRange->WrappedlessOrEqual((AbstractValue*)I2) && I2->WrappedlessOrEqual((AbstractValue*)knownRange)) {
                // not equal?
                knownValGroup.second.insert(currChkVal);
              } else {              
                StridedWrappedRange meetRes = StridedWrappedMeet(knownRange, I2);
                // intersection.
                if(!meetRes.isBot()) {
                  knownValGroup.second.insert(currChkVal);
                }
              }
            }
              
          }

          

          for(std::pair<const Value*, std::set<const Value*> > &currWrappedGroup: wrappedValueGroups) {
            if(currWrappedGroup.second.size() < totalValues.size()) {
              numberWrappedImpropedAlias++;
            }
          }

          for(std::pair<const Value*, std::set<const Value*> > &currStidedGroup: stridedValueGroups) {
            if(currStidedGroup.second.size() < totalValues.size()) {
              numberStridedImprovedAlias++;
            }
          }

        }
    }

    void compareTwoIntervals(WrappedRange *I1, StridedWrappedRange* I2, bool isSigned){
    
      //dbgs() << "Comparing:" << *I1 << ":" << *I2 << "\n";
      assert(I1); assert(I1->getWidth() == I2->getWidth());
      assert(I2); assert(I1->getValue() == I2->getValue());
      
      I1->normalize();
      I2->normalize();
      NumTotal++;

      if (I1->IsTop() && I2->IsTop()){
	NumOfTrivial++;
	return;
      }

      if (I1->isBot() || I2->isBot()){
	NumOfTrivial++;
	return;
      }
            
      uint64_t val_I1 = I1->Cardinality();
      uint64_t val_I2 = I2->Cardinality();
      uint64_t diff;
      if (val_I1 > val_I2)
        diff = val_I1 - val_I2;
      else
        diff = val_I2 - val_I1;
      
      if (diff <= PRECISION_TOLERANCE){
        //dbgs() << "Same PREC\n";
      	NumOfSame++;
      	return;
      }
      
      if (I1->IsTop() && !I2->IsTop()){
#ifdef VERBOSE
        dbgs() << "Strided Wrapped more precise: ";
        I2->print(dbgs());
        dbgs() << " < ";
        I1->print(dbgs());
        dbgs() << "\n";
        dbgs() << "METADATA\n";
        
       for (Function::iterator b = I2->getBasicBlock()->getParent()->begin(), be = I2->getBasicBlock()->getParent()->end(); b != be; ++b) {
           BasicBlock *bbPtr = &(*b);
           for (BasicBlock::iterator i = bbPtr->begin(), e = bbPtr->end(); i != e; ++i) {
                Instruction* iPtr = &(*i);
                dbgs() << *iPtr << "\n";
           }

       }

        /*Function::BasicBlockListType &Blocks = I2->getBasicBlock()->getParent()->getBasicBlockList();     
        for (BasicBlock::iterator bb = Blocks.begin(), be = Blocks.end(); bb != be; ++bb) {
           BasicBlock *bbblock = &bb;
            for (BasicBlock::iterator i = bbblock->begin(), e = bbblock->end(); i != e; ++i) {
          Instruction* ii = &(*i);
          //here
        }

          // for(Instruction &i: bb.getInstList()) {
            //Instruction *ii = &*bb;
            
          // dbgs() << *bb << "\n";
          // for (BasicBlock::iterator i = bb.begin(), e = bb->end(); i != e; ++i) {
          // Instruction* ii = &*i;
          // dbgs() << *ii << "\n";
          // }
          // }
        }*/
        dbgs() << "ENDMETADATA\n";
#endif 
        NumWrappedIsBetter1++;
        return;
      }
      
      if (!I1->IsTop() && I2->IsTop()){
#ifdef VERBOSE
	dbgs() << "Classical more precise: ";
	I1->print(dbgs());
	dbgs() << " < ";
	I2->print(dbgs());
	dbgs() << "\n";
#endif 
	NumUnWrappedIsBetter++;
	return;
      }
      
      APInt a = I1->getLB();
      APInt b = I1->getUB();
      WrappedRange NewI1(a,b,a.getBitWidth());
      if (I1->isBot()) NewI1.makeBot();
      if (I1->IsTop()) NewI1.makeTop();
      if (I2->getLB() == NewI1.getLB() && I2->getUB() == NewI1.getUB() && I2->getStride() <= 1) {
        //dbgs() << "Same1\n";
	NumOfSame++;
	return;
      }
      
      
      WrappedRange NewI2(I2->getLB(),I2->getUB(),I2->getLB().getBitWidth());
      
    NewI2.setStride(I2->getStride());
    
      if ( (I2->isMoreOrEqualPrecise(&NewI1))){
	if (NewI1.isMoreOrEqualPrecise(I2)) {
	
	  NumOfSame++;
	  //dbgs() << "Same2\n";
	} else{
#ifdef VERBOSE
	  dbgs() << "Strided Wrapped more precise: ";
	  I2->print(dbgs());
	  dbgs() << " < ";
	  NewI1.print(dbgs());
	  dbgs() << "\n";
        dbgs() << "METADATA\n";
        
       for (Function::iterator b = I2->getBasicBlock()->getParent()->begin(), be = I2->getBasicBlock()->getParent()->end(); b != be; ++b) {
         BasicBlock *bbPtr = &(*b);
         for (BasicBlock::iterator i = bbPtr->begin(), e = bbPtr->end(); i != e; ++i) {
           Instruction* iPtr = &(*i);
           dbgs() << *iPtr << "\n";
           }
         
       }
        
        dbgs() << "ENDMETADATA\n";

#endif 
	  NumWrappedIsBetter2++;
	}
      }
      else{
      
	if (NewI1.isMoreOrEqualPrecise(I2)){
#ifdef VERBOSE
	  dbgs() << "Classical more precise: ";
	  NewI1.print(dbgs());
	  dbgs() << " < ";
	  I2->print(dbgs());
	  dbgs() << "\n";
#endif 
	  NumUnWrappedIsBetter++;
	}
	else
	  NumOfIncomparable++;
      }      
    } // end function

    void printStats(raw_ostream &Out){
      Out << "=----------------------------------------------------------------------=\n";
      Out << "                         Summary results                                \n";
      Out << "=----------------------------------------------------------------------=\n";
      Out << "# tracked intervals                         : "  
	  <<  NumTotal  << "\n";
      Out << "# proper wrapped intervals                : "  
	  <<  NumTotal - NumOfTrivial - NumWrappedIsBetter1 << "\n";
      Out << "# proper Strided wrapped intervals                  : "  
	  <<  NumTotal - NumOfTrivial << "\n";
      Out << "# strided wrapped < wrapped                       : " 
	  <<  NumWrappedIsBetter1+NumWrappedIsBetter2 
	  << " (tolerance=" <<  PRECISION_TOLERANCE << ")\n";
      // Out << "# proper intervals                          : "  
      // 	  <<  NumTotal - NumOfTrivial << "\n";
      // Out << "# wrapped == unwrapped                      : " 
      // 	  <<  NumOfSame << " (tolerance=" <<  PRECISION_TOLERANCE << ")\n";
      // Out << "# wrapped < unwrapped (unwrappred=[-oo,oo]) : "  
      // 	  <<  NumWrappedIsBetter1   << "\n";     
      // Out << "# wrapped < unwrapped (unwrappred!=[-oo,oo]): "  
      // 	  <<  NumWrappedIsBetter2   << "\n";     
      Out << "# wrapped < strwrapped                       : "  
	  <<  NumUnWrappedIsBetter << "    // should be 0. \n";
      Out << "# Strided Alias Improved:" << numberStridedImprovedAlias << "\n";
      Out << "# Wrapped Alias Improved:" << numberWrappedImpropedAlias << "\n";
      Out << "=----------------------------------------------------------------------=\n";

    }
   
  }; // end of class runPrecComparison


  // This pass aims at counting the number of redundant runtime checks
  // generated by the IOC tools that can be identified by both
  // classical fixed-width and wrapped interval analyses.
  class runIOC : public ModulePass{
  public:
    class IOCCounter{
    public:
      IOCCounter():
	NumTrapBlocks(0), 
	NumReachableTrapBlocks(0), 
	NumUnreachableTrapBlocks(0){}
      unsigned int NumTrapBlocks;
      unsigned int NumReachableTrapBlocks;
      unsigned int NumUnreachableTrapBlocks;
    };
    class IOCCounter_Unwrapped: public IOCCounter{ 
    public:
      IOCCounter_Unwrapped(): IOCCounter(){
      }
    };
    class IOCCounter_Wrapped  : public IOCCounter{ 
    public:
      IOCCounter_Wrapped(): IOCCounter(){
      }
    };

    /// Pass identification, replacement for typeid    
    static char ID; 
    /// Constructor of the class.
    runIOC() :  ModulePass(ID), IsSigned(true) { }
    /// Destructor of the class.
    ~runIOC(){}
    
    virtual bool runOnModule(Module &M){
     
      AliasAnalysis *AA = &getAnalysis<AliasAnalysis>(); 
      CallGraph     *CG = &getAnalysis<CallGraph>();

      recordTrapBlocks(M,CG);
      
      RangeAnalysis      Unwrapped(&M, widening, narrowing, AA, IsSigned);
      WrappedRangeAnalysis Wrapped(&M, widening, narrowing, AA);
      IOCCounter_Unwrapped c1; IOCCounter_Wrapped c2;

      if (runOnlyFunction != ""){
	Function *F = M.getFunction(runOnlyFunction); 
	if (!F){
	  dbgs() << "ERROR: function " << runOnlyFunction << " not found\n\n";
	  return false;
	}
	else{
	  Unwrapped.init(F); 
	  Unwrapped.solve(F);
	  Wrapped.init(F); 
	  Wrapped.solve(F);
	  updateCounters(c1,c2,Unwrapped,Wrapped,F);

	}
      }
      else{
	int k=0;
	for (Module::iterator F = M.begin(), FE = M.end(); F != FE ; ++F){
	  if (IsAnalyzable(F,*CG)){
	    if ( (numFuncs > 0) && (k > numFuncs)) 
	      break;
#if 1
	    dbgs() << k << ": analysis of  " << F->getName() << "\n";
	    dbgs() << "Running unwrapped ... \n";
#endif 
	    Unwrapped.init(F); 
	    Unwrapped.solve(F);
#if 1
	    dbgs() << "Running wrapped ... \n";
#endif 
	    Wrapped.init(F); 
	    Wrapped.solve(F);
#if 1
	    dbgs() << "Updating counters ... \n";
#endif 
	    updateCounters(c1,c2,Unwrapped,Wrapped,F);
	    k++;
	  }
	}
      }
      printStats(dbgs(), c1, c2);
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage& AU) const {
      RangePassRequirements(AU);
    }
    
  private:
    bool IsSigned;
    DenseMap<BasicBlock*,unsigned int> TrackedTrapBlocks;
    
    void recordTrapBlocks(Module &M, CallGraph *CG){
      for (Module::iterator F = M.begin(), FE = M.end(); F != FE; ++F){
	if (IsAnalyzable(F,*CG)){
	  for (Function::iterator B = F->begin(), BE = F->end(); B != BE; ++B){
	    for (BasicBlock::iterator I = B->begin(), IE = B->end(); I != IE; ++I){
	      if (CallInst *CI = dyn_cast<CallInst>(&*I)){
		if (Function *F = CI->getCalledFunction()){
		  if (F->getName().endswith("trap_handler"))
		    TrackedTrapBlocks.insert(std::make_pair(B,0));
		}
	      }
	    }
	  }
	}
      }
    }

    inline bool isTrapBlock(BasicBlock *BB){
      DenseMap<BasicBlock*,unsigned int>::iterator It = 
         TrackedTrapBlocks.find(BB);
      return (It != TrackedTrapBlocks.end());
    }

    void updateCounters(IOCCounter_Unwrapped &c1, IOCCounter_Wrapped &c2,
			RangeAnalysis &a1       , WrappedRangeAnalysis &a2,
			Function *F){
      for (Function::iterator BB = F->begin(), BE = F->end(); BB != BE; ++BB){
	if (isTrapBlock(BB)){
	  c1.NumTrapBlocks++;
	  c2.NumTrapBlocks++;
	  if (a1.IsReachable(BB))
	    c1.NumReachableTrapBlocks++;
	  else
	    c1.NumUnreachableTrapBlocks++;
	  if (a2.IsReachable(BB))
	    c2.NumReachableTrapBlocks++;
	  else
	    c2.NumUnreachableTrapBlocks++;
	}
      }
    }

    void printStats(raw_ostream &Out, 
		    const IOCCounter_Unwrapped &unwrapped, 
		    const IOCCounter_Wrapped &wrapped){

      assert(unwrapped.NumTrapBlocks == wrapped.NumTrapBlocks);
      Out << "=----------------------------------------------------------------------=\n";
      Out << "                        Summary results                                 \n";
      Out << "=----------------------------------------------------------------------=\n";
      Out << "Total number of IOC trap blocks              : " 
	  << unwrapped.NumTrapBlocks << "\n";
      Out << "Num of reachable   trap blocks with UNWRAPPED: " 
       	  << unwrapped.NumReachableTrapBlocks  << "\n";
      Out << "Num of unreachable trap blocks with UNWRAPPED: " 
       	  << unwrapped.NumUnreachableTrapBlocks  << "\n";
      Out << "Num of reachable   trap blocks with WRAPPED  : " 
       	  << wrapped.NumReachableTrapBlocks  << "\n";     	  
      Out << "Num of unreachable trap blocks with WRAPPED  : " 
       	  << wrapped.NumUnreachableTrapBlocks  << "\n";     	  
      Out << "=----------------------------------------------------------------------=\n";
    }

  }; // end of class runIOC

  /// These passes are for generating number of experiments in papers.
  /// Regular users do not need to know about them.

  char runPrecComparison::ID = 0;
  static RegisterPass<runPrecComparison> 
  RunPrecision("compare-range-analyses",
	       "Comparison -range-analysis vs -wrapped-range-analysis.",
	       false,false);

char runBintComparison::ID = 0;
  static RegisterPass<runBintComparison> 
  RunPrecision1("compare-strided-range-analyses",
	       "Comparison -wrapped-range-analysis vs -strided-wrapped-range-analysis.",
	       false,false);

  char runIOC::ID = 0;
  static RegisterPass<runIOC> 
  RunIOC("ioc-stats", "Run IOC experiment.", false, false);


  // class CountNumFuncs : public ModulePass{
  // public:
  //   // Pass identification, replacement for typeid    
  //   static char ID; 
  //   /// Constructor of the class.
  //   CountNumFuncs() :  ModulePass(ID), numfuncs(0) { }
  //   /// Destructor of the class.
  //   ~CountNumFuncs(){}
    
  //   virtual bool runOnModule(Module &M){
  //     CallGraph     *CG = &getAnalysis<CallGraph>();
  //     for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F){	  
  // 	if (IsAnalyzable(F,*CG))
  // 	  numfuncs++;
  //     } // end for
  //     dbgs() << "Num of functions " << numfuncs << "\n";
  //     return false;
  //   }
    
  //   virtual void getAnalysisUsage(AnalysisUsage& AU) const {
  //     RangePassRequirements(AU);
  //   }    
  // private:
  //   unsigned int numfuncs;
    
  // }; 

  // char CountNumFuncs::ID = 0;
  // static RegisterPass<CountNumFuncs> 
  // CountNumFuncs("numfuncs", "Count number of functions.", false, false);


  // class printFunction : public ModulePass{
  // public:
  //   // Pass identification, replacement for typeid    
  //   static char ID; 
  //   /// Constructor of the class.
  //   printFunction() :  ModulePass(ID) { }
  //   /// Destructor of the class.
  //   ~printFunction(){}
    
  //   virtual bool runOnModule(Module &M){
  //     if (runOnlyFunction != ""){
  // 	Function *F = M.getFunction(runOnlyFunction); 
  // 	if (!F){ 
  // 	  dbgs() << "ERROR: function " << runOnlyFunction << " not found\n\n";
  // 	  return false;
  // 	}
  // 	for (Function::iterator i = F->begin(), e = F->end(); i != e; ++i)
  // 	  dbgs() << *i ;
  //     }      
  //     return false;
  //   }
    
  //   virtual void getAnalysisUsage(AnalysisUsage& AU) const {
  //     RangePassRequirements(AU);
  //   }    
  // }; 

  // char printFunction::ID = 0;
  // static RegisterPass<printFunction> 
  // printFunction("printfunc", "Print a selected function.", false, false);

} // end namespace





