// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file FixpointSSI.cpp
///       Iterative Forward Abstract Interpreter 
//////////////////////////////////////////////////////////////////////////////
///
/// The fixpoint is intraprocedural and does not track any memory
/// location. Thus, it considers only variables in SSA form.
///
/// The precision of the fixpoint relies heavily on the effectiveness
/// of the SSI form. That is, it is vital for the analysis that the
/// SSI form pass is able to add as many sigma nodes as possible.
/// - We have noticed that the use of CFGSimplify can avoid the SSI pass
///   to add sigma nodes losing dramatically precision.
/// - It is relative often code like the following:
///
/// \verbatim
///  %tmp7 = sext i8 %x to i32
///  %tmp8 = sext i8 -10 to i32
///   ...
///  %tmp9 = icmp sge i32 %tmp7, %tmp8
///  ... in another block:
///  %sigma = phi i8 [%x,..]
/// \endverbatim
///
///  Here there is type mismatch for %x. In these case, we do not call
///  visitSigmaNode.
///
/// Another source of imprecision is cast instructions from floating
/// or pointers to integers which are not tracked by the analysis.
///
/// \todo Make sure there is no memory leaks.
///
/// The fixpoint is mostly designed for running a lattice. However, it
/// can also run non-lattice abstract domains if some special care is
/// taken. In particular:
/// - if the abstract domain is not a lattice widening cannot be
///   executed in a intermittent manner. Otherwise, the analysis may
///   not terminate.
/// - Specialized versions of joins to merge more than two abstract
///   values are recommended to avoid losing precision since joins are
///   not associative.
/////////////////////////////////////////////////////////////////////////////////
#include "FixpointSSI.h"
#include "AbstractValue.h"
#include "ArrayIndexManager.h"

using namespace llvm;
using namespace unimelb;
using namespace NEWEVAL;

STATISTIC(NumOfAnalFuncs     ,"Number of analyzed functions");
STATISTIC(NumOfAnalBlocks    ,"Number of analyzed blocks");
STATISTIC(NumOfAnalInsts     ,"Number of analyzed instructions");
STATISTIC(NumOfInfeasible    ,"Number of infeasible branches");
STATISTIC(NumOfWideningPts   ,"Number of widening locations");
STATISTIC(NumOfWidenings     ,"Number of widen instructions");
STATISTIC(NumOfNarrowings    ,"Number of narrowing passes");
STATISTIC(NumOfSkippedIns    ,"Number of skipped instructions");

// Debugging
void printValueInfo(Value *,Function*);
void printUsersInst(Value *,SmallPtrSet<BasicBlock*, 16>,bool);
inline void PRINTCALLER(std::string s){ /*dbgs() << s << "\n";*/ }

FixpointSSI::
FixpointSSI(Module *M,  unsigned WL, unsigned NL, AliasAnalysis *AA,
	    OrderingTy ord):
  M(M),
  WideningLimit(WL),
  ConstSetOrder(ord),
  NarrowingLimit(NL),
  NarrowingPass(false),
  AA(AA),
  IsAllSigned(true){
  if (WideningLimit == 0)
    dbgs() << "Warning: user selected no widening!\n";
  if (NarrowingLimit == 0)
    dbgs() << "Warning: user selected no narrowing!\n";

}

FixpointSSI::
FixpointSSI(Module *M, unsigned WL, unsigned NL, 
	    AliasAnalysis *AA, bool isSigned,
	    OrderingTy ord):
  M(M),
  WideningLimit(WL),
  ConstSetOrder(ord),
  NarrowingLimit(NL),
  NarrowingPass(false),
  AA(AA),
  IsAllSigned(isSigned){
  if (WideningLimit == 0)
    dbgs() << "Warning: user selected no widening!\n";
  if (NarrowingLimit == 0)
    dbgs() << "Warning: user selected no narrowing!\n";
  }

FixpointSSI::~FixpointSSI(){
  for (AbstractStateTy::iterator 
	 I = ValueState.begin(), 
	 E=ValueState.end(); I!=E; ++I)
    delete I->second;
  for (DenseMap<Value*,TBool*>::iterator 
	 I=TrackedCondFlags.begin(), 
	 E=TrackedCondFlags.end(); I!=E; ++I)
    delete I->second;

  ConstSet.clear();
}

void FixpointSSI::init(Function *F){

  Cleanup();
  // Pessimistic assumption about trackable global variables. In this
  // case, no bother running an expensive alias analysis.
  // addTrackedGlobalVariablesPessimistically(M);
  unsigned Width;
  Type * Ty;
  if (Utilities::IsTrackableFunction(F)){
    // Add formal parameters as definitions and initialize the
    // abstract value
    for (Function::arg_iterator 
	   argIt=F->arg_begin(),E=F->arg_end(); argIt != E; argIt++) {
      DEBUG(printValueInfo(argIt,F));
      if (isCondFlag(argIt)){
	DEBUG(dbgs() << "\trecording a Boolean flag:" 
	      << argIt->getName() << "\n");
	TrackedCondFlags.insert(std::make_pair(&*argIt, new TBool()));
      }
      else{
	if (Utilities::getTypeAndWidth(argIt, Ty, Width)){
	  AbstractValue *Top = initAbsValTop(argIt);
	  Top->setBasicBlock(&F->getEntryBlock());
	  ValueState.insert(std::make_pair(&*argIt,Top));      
	}
      }
    } // end for

    ArrayIndexClassifier::setupFunction(F);
    
    // Add instructions as definitions and initialize the abstract value
    for (inst_iterator I = inst_begin(F), E=inst_end(F) ; I != E; ++I){
      DEBUG(printValueInfo(&*I,F));
      if (HasLeftHandSide(*I)){
	if (Value * V = dyn_cast<Value>(&*I)){
	  if (isCondFlag(V)){
	    DEBUG(dbgs() << "\trecording a Boolean flag:" << V->getName() << "\n");
	    TrackedCondFlags.insert(std::make_pair(&*V, new TBool()));
	  }	
	  else{
	    if (Utilities::getTypeAndWidth(V, Ty, Width)){
	      AbstractValue *Bot = initAbsValBot(V);
	      Bot->setBasicBlock(I->getParent());
	      ValueState.insert(std::make_pair(&*V,Bot));      	
	    }
	  }
	}
      }
    } // end for    
    
    /// Record all constant integers that appear in the program.
    /// We put them into a set first to eliminate duplicates.
    std::set<int64_t> Set;
    Utilities::recordIntegerConstants(F,Set);
    std::copy(Set.begin(), Set.end(), std::back_inserter(ConstSet));
    // Sort them
    if (ConstSetOrder == LESS_THAN){
      // Since Set is ordered already using signed < we don't need to
      // do anything here.
      // std::sort(ConstSet.begin(), ConstSet.end()); 
    }
    else if (ConstSetOrder == LEX_LESS_THAN)
      std::sort(ConstSet.begin(), ConstSet.end(), Utilities::Lex_LessThan_Comp);
    else 
      llvm_unreachable("Unsupported ordering");
    DEBUG(Utilities::printIntConstants(ConstSet));

    /// Create an abstract value for each integer constant in the
    /// program.
    std::vector<std::pair<Value*,ConstantInt*> > NewAbsVals;
    Utilities::addTrackedIntegerConstants(F, IsAllSigned, NewAbsVals); 
    for (unsigned int i=0; i<NewAbsVals.size(); i++){
      ValueState.insert(std::make_pair(NewAbsVals[i].first,
				       initAbsIntConstant(NewAbsVals[i].second)));   
    }
    // Record widening points.
    addTrackedWideningPoints(F);      

#ifdef SKIP_TRAP_BLOCKS
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
#endif     
  }
}


// Iterative intraprocedural fixpoint + narrowing.
void FixpointSSI::solve(Function *F){
  solveLocal(F);
  computeNarrowing(F);
}

// Compute a intraprocedural fixpoint until no change applying the
// corresponding transfer function.
void FixpointSSI::solveLocal(Function *F){
  DEBUG(dbgs () << "Starting fixpoint for " << F->getName() << " ... \n");
  NumOfAnalFuncs++;

  // Confirm this: no needed for intraprocedural analysis
  // We need to cleanup BBExecutable and KnownFeasibleEdges in case
  // the function is analyzed more than once. Otherwise, after the
  // first time all blocks are kept as processed so nothing will be
  // done. 
  //cleanupPreviousFunctionAnalysis(F);
  markBlockExecutable(&F->getEntryBlock());    
  computeFixpo();
  DEBUG(dbgs () << "Fixpoint reached for " << F->getName() << ".\n");
}

void FixpointSSI::computeFixpo(){
  // Process the work lists until they are empty!
  while (!BBWorkList.empty() || !InstWorkList.empty()) {
    // Process the instruction work list.
    while (!InstWorkList.empty()) {
      std::set<Value*>::iterator It = InstWorkList.begin();
      InstWorkList.erase(It);
      Value *I = *It;
      // "I" got into the work list because it made a transition.  See
      // if any users are both live and in need of updating.
      DEBUG(dbgs() << "\n*** Popped off I-WL: " << *I << "\n");      
      DEBUG(printUsersInst(I,BBExecutable,true));
      for (Value::use_iterator UI = I->use_begin(), E = I->use_end();
           UI != E; ++UI) {
        Instruction *U = cast<Instruction>(*UI);
	// We check that the instruction U is defined in an executable
	// block
        if (BBExecutable.count(U->getParent()) && U != I) {
	  DEBUG(dbgs() << "\n***Visiting: " << *U << " as user of " 
		<< *I << "\n"); 
          visitInst(*U);
	}
      } // end for

      /// We need to pay special attention to sigma nodes for two
      /// reasons. For code like this:
      /// \verbatim
      /// i = phi [tmp6,...] [0,...]
      /// ...
      /// sigma  = phi [i,...]
      /// tmp6 = add sigma, 1
      /// \endverbatim
      /// Assume that tmp6 changes from [0,0] to [1,1]. As a result,
      /// we push tmp6 into IWorklist. Then, we analyze i and infer
      /// than i=[0,1], and push i also in the IWorklist. If we pop
      /// first tmp6 from IWorklist then tmp6 is again [1,1] since
      /// sigma was not updated. This suggests that we should visit
      /// first sigma nodes.  Another issue arises with code like this:
      /// \verbatim
      /// tmp4  = icmp slt i, j
      /// ....
      /// sigma =  phi [i,..]
      /// \endverbatim
      /// Here sigma is an user of i. However, sigma is also indirectly
      /// an user of j. That is, if j is modified we should re-analyze
      /// sigma. However, this dependency between j and sigma does not
      /// appear in the def-use information.  We solve in a bit clumsy
      /// way these two issues by tracking a map from V to set(V) that
      /// keeps track of for a given variable V which is the set of
      /// sigma nodes that should be re-analyzed.
      ///
      /// \bug: we are visiting twice the number of sigma nodes.
      if (SmallValueSet * SigmaSet = TrackedValuesUsedSigmaNode[I]){
	for( SmallValueSet::iterator UI = SigmaSet->begin(),
	       UE = SigmaSet->end(); UI != UE; ++UI){
	  Instruction * U = cast<Instruction>(*UI);
	  if (BBExecutable.count(U->getParent())) {
	    DEBUG(dbgs() << "\n***Forcing the visit of: " << *U 
		  << " as user of " << *I << "\n");      
	    visitInst(*U);
	  }
	} // end inner for
      }      
    } // end while

    // Process the basic block work list.
    while (!BBWorkList.empty()) {
      std::set<BasicBlock*>::iterator BBIt = BBWorkList.begin();
      BBWorkList.erase(BBIt);
      BasicBlock *BB = *BBIt;
      DEBUG(dbgs() << "\n***Popped off BBWL: " << *BB);
      // Notify all instructions in this basic block that they are newly
      // executable.
      for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I){
        visitInst(*I);
      }
    } // end while
  } // end outer while
}

/// Iterate over all instructions in the function and apply the
/// corresponding transfer function for every one without
/// widening. The instructions must be visited preserving the original
/// order in the program.
/// \lambda x. x /\ F(x)
void FixpointSSI::computeOneNarrowingIter(Function *F){
  markBlockExecutable(&F->getEntryBlock());    
  // Iterator dfs over the basic blocks in the function
  for (df_iterator<BasicBlock*>  DFI = df_begin(&F->getEntryBlock()), 
 	                         DFE = df_end(&F->getEntryBlock()); 
       DFI != DFE; ++DFI) {  

    BasicBlock * BB = *DFI;
    if (BBExecutable.count(BB)){
      for (BasicBlock::iterator I = BB->begin(), E = BB->end(); 
	   I != E; ++I){
	  visitInst(*I);
      }
    }
  }
}

// Narrowing is implemented by making a arbitrary number of passes
// applying the transfer functions **without** applying widening.
void FixpointSSI::computeNarrowing(Function *EntryF){

  if (NarrowingLimit == 0) return;

  unsigned N = NarrowingLimit;
  NarrowingPass=true;

  // We should clear these datastructures before starting narrowing.
  // Otherwise, narrowing cannot make unreachable a block that was
  // reachable for the fixpoint.
  // BBExecutable.clear();
  // KnownFeasibleEdges.clear();

  while (N-- > 0){
    DEBUG(dbgs () << "\nStarting narrowing  ... \n");
    NumOfNarrowings++;    
    assert(InstWorkList.empty() && "The worklist should be empty");
    computeOneNarrowingIter(EntryF);
    assert(InstWorkList.empty() && "The worklist should be empty");
  } 
  NarrowingPass=false;
  DEBUG(dbgs () << "Narrowing finished.\n");
}

bool FixpointSSI::
isEdgeFeasible(BasicBlock *From, BasicBlock *To){
  std::set<Edge>::iterator 
    I =  KnownFeasibleEdges.find(std::make_pair(From,To));  
  if (I != KnownFeasibleEdges.end()) 
    return true;
  else{   
    NumOfInfeasible++;		  
    return false;
  }
}

// Check if the new value is contained by the old value. If yes, then
// return and do nothing.  Otherwise, add the instruction in the
// worklist and apply widening if widening conditions are
// applicable. If we are doing a narrowing pass then widening is
// disabled and we don't add anything in the worklist.
void FixpointSSI::updateState(Instruction &Inst, AbstractValue * NewV) {

  assert(NewV != NULL && "updateState: instruction not defined"); 
  AbstractStateTy::iterator I = ValueState.find(&Inst);
  AbstractValue* OldV  = I->second;

  // DEBUG(dbgs() << "Old value: " );
  // DEBUG(OldV->print(dbgs()));
  // DEBUG(dbgs() << "\n" );
  // DEBUG(dbgs() << "New value: " );
  // DEBUG(NewV->print(dbgs()));
  // DEBUG(dbgs() << "\n" );

  if (NarrowingPass){
    DEBUG(dbgs() << "***[Narrowing] from ");
    DEBUG(OldV->print(dbgs()));
    DEBUG(dbgs() << " to " );
    DEBUG(NewV->print(dbgs()));
    DEBUG(dbgs() << "\n" );
    assert(NewV);
    delete ValueState[&Inst];
    ValueState[&Inst] = NewV;
  }
  else{
    ////////////////////////////////////////////////////////////////////
    // Widening:
    //             bottom         if n=0
    // f^{n}_{w} = f^{n-1}_{w}    if n>0 and 
    //                            f(f^{n-1}_{w}) \subseteq f^{n-1}_{w}
    //             widening(f^{n-1}_{w},f(f^{n-1}_{w})) otherwise
    // Here OldV = f^{n-1}_{w} and NewV = f(f^{n-1}_{w})
    ////////////////////////////////////////////////////////////////////
    
    if (I != ValueState.end() && NewV->lessOrEqual(OldV)){
      // No change
      DEBUG(dbgs() << "\nThere is no change\n");
      // If uncommented then we produce a seg fault if debugging mode
      // delete NewV
      return;  
    }
    
    NewV->incNumOfChanges();        
    if (Widen(&Inst,NewV->getNumOfChanges())){
      //dbgs() << "WIDENING " <<  Inst << "\n";

      NumOfWidenings++;
      NewV->widening(OldV,ConstSet);
      // We reset the counter because we don't want to apply widening
      // if not really needed. E.g., after a widening we can have a
      // casting operation. If the counter is not reset then we will
      // do widening again with potential catastrophic losses.
      if (NewV->isLattice())
	NewV->resetNumOfChanges();
    }
    // there is change: visit uses of I.
    assert(NewV);

    delete ValueState[&Inst];
    ValueState[&Inst] = NewV;
    DEBUG(dbgs() << "***Added into I-WL: " << Inst << "\n");
    InstWorkList.insert(&Inst);
  }
}

// Special case for Boolean flags.
void FixpointSSI::updateCondFlag(Instruction &I, TBool * New){  
  assert(isTrackedCondFlag(&I));  
  if (NarrowingPass){
    delete TrackedCondFlags[&I];
    TrackedCondFlags[&I] = New;    
    return;
  }  
  TBool * Old = TrackedCondFlags.lookup(&I);  
  if (Old->isEqual(New)){
    // No change
    DEBUG(dbgs() << "\nThere is no change\n");
    //delete New;
    return;  
  }  
  // There is change: visit uses of I.
  delete TrackedCondFlags[&I];
  TrackedCondFlags[&I] = New;
  DEBUG(dbgs() << "***Added into I-WL: " << I << "\n");
  InstWorkList.insert(&I);
}

// Mark the edge Source-Dest as executable and mark Dest as an
// executable block.  Moreover, we revisit the phi nodes of Dest.
void FixpointSSI::markEdgeExecutable(BasicBlock *Source, BasicBlock *Dest) {
  if (!KnownFeasibleEdges.insert(std::make_pair(Source, Dest)).second)
    return;  // This edge is already known to be executable!  

  DEBUG(dbgs() << "***Marking Edge Executable: " << Source->getName()
	       << " -> " << Dest->getName() << "\n");
  if (BBExecutable.count(Dest) && !NarrowingPass) {
    // The destination is already executable, but we just made an edge
    // feasible that wasn't before.  Revisit the PHI nodes in the block
    // because they have potentially new operands.
    for (BasicBlock::iterator I = Dest->begin(), E = Dest->end(); I!=E ; ++I){
      if (isa<PHINode>(I)){
	DEBUG(dbgs() << "Triggering the analysis of " << *I << "\n");
	visitPHINode(*cast<PHINode>(I));    
      }
    }
  } 
  else 
    markBlockExecutable(Dest);
}

// Mark a basic block as executable, adding it to the BB worklist if
// it is not already executable.
void FixpointSSI::markBlockExecutable(BasicBlock *BB) {
  DEBUG(dbgs() << "***Marking Block Executable: " << BB->getName() << "\n");
  NumOfAnalBlocks++;  
  BBExecutable.insert(BB);   // Basic block is executable  

#ifdef SKIP_TRAP_BLOCKS
  DenseMap<BasicBlock*,unsigned int>::iterator It = TrackedTrapBlocks.find(BB);
  if (It != TrackedTrapBlocks.end())
    return;
#endif 
  BBWorkList.insert(BB);     // Add the block to the work list
}

// visitInst - Execute the instruction
void FixpointSSI::visitInst(Instruction &I) { 

  NumOfAnalInsts++;

  // First, special instructions handled directly by the fixpoint
  // algorithm, never passed into the underlying abstract domain
  // because they can be defined in terms of join, meet, etc.

  if (StoreInst *SI  = dyn_cast<StoreInst>(&I))
    return visitStoreInst(*SI);

  if (LoadInst *LI   = dyn_cast<LoadInst>(&I))
    return visitLoadInst(*LI);

  if (CallInst *CI = dyn_cast<CallInst>(&I))
    return visitCallInst(*CI);

  if (ReturnInst *RI = dyn_cast<ReturnInst>(&I))
    return visitReturnInst(*RI);

  if (PHINode *PN = dyn_cast<PHINode>(&I))
    return visitPHINode(*PN);

  if (SelectInst *SelI = dyn_cast<SelectInst>(&I))
    return visitSelectInst(*SelI);

  if (TerminatorInst *TI = dyn_cast<TerminatorInst>(&I))
    return visitTerminatorInst(*TI);

  if (ICmpInst *ICmpI = dyn_cast<ICmpInst>(&I))
    return visitComparisonInst(*ICmpI);
  
  if (IsBooleanLogicalOperator(&I))
    return visitBooleanLogicalInst(I);
  
  // Otherwise, we pass the transfer function to the abstract domain.
  if (Value *V = dyn_cast<Value>(&I)){
    if (AbstractValue * AbsV = ValueState.lookup(V)){ 

      // New is going to keep a pointer to a derived class. The
      // methods visitArithBinaryOp, visitBitwiseBinaryOp, and
      // visitCast ensure that it is new allocated memory.
      AbstractValue *New = NULL;
      switch (I.getOpcode()){
      case Instruction::Add: 
      case Instruction::Sub:
      case Instruction::Mul:
      case Instruction::SDiv:
      case Instruction::UDiv:
      case Instruction::SRem:
      case Instruction::URem:
	{
	  DEBUG(dbgs() << "Arithmetic instruction: " << I << "\n");
	  /// 
	  // We can have instructions like 
	  // %tmp65 = sub i32 %tmp64, ptrtoint ([6 x %struct._IO_FILE*]* @xgets.F to i32)	    
	  // Therefore, we need to check if the operands are in
	  // ValueState. If not, just top.
	  ////
	  AbstractValue * Op1 = Lookup(I.getOperand(0), false);
	  AbstractValue * Op2 = Lookup(I.getOperand(1), false);
	  if (Op1 && Op2)
	    New = AbsV->visitArithBinaryOp(Op1,Op2,
					   I.getOpcode(),I.getOpcodeName());
	  else{
	    New = AbsV->clone();
	    New->makeTop();	      
	  }
	}
	break;
      case Instruction::Shl:  // logical left shift
      case Instruction::LShr: // logical right shift    
      case Instruction::AShr: // arithmetic right shift    
      case Instruction::And:  // bitwise and
      case Instruction::Or:   // bitwise or
      case Instruction::Xor:  // bitwise xor
	{
	  DEBUG(dbgs() << "Bitwise instruction: " << I << "\n");
	  AbstractValue * Op1 = Lookup(I.getOperand(0), false);
	  AbstractValue * Op2 = Lookup(I.getOperand(1), false);
	  if (Op1 && Op2)
	    New =  AbsV->visitBitwiseBinaryOp(Op1, Op2,
					      I.getOperand(0)->getType(), 
					      I.getOperand(1)->getType(),
					      I.getOpcode(), I.getOpcodeName());
	  else{
	    New = AbsV->clone();
	    New->makeTop();	      
	  }
	}
	break;
      case Instruction::BitCast: // no-op cast from one type to another
      case Instruction::ZExt:    // zero extend integers
      case Instruction::SExt:    // sign extend integers
      case Instruction::Trunc:   // truncate integers
	{
	  DEBUG(dbgs() << "Casting instruction: " << I << "\n");	    
	  // Tricky step: the source of the casting instruction may be
	  // a Boolean Flag.  If yes, we need to convert the Boolean
	  // flag into an abstract value. This must be done by the
	  // class that implements AbstractValue.
	  TBool * SrcFlag  = NULL;
	  AbstractValue *SrcAbsV = NULL;	  
	  if (isTrackedCondFlag(I.getOperand(0)))
	    SrcFlag = TrackedCondFlags.lookup(I.getOperand(0));
	  else
	    SrcAbsV = Lookup(I.getOperand(0), false);

	  if (SrcFlag || SrcAbsV)
	    New =  AbsV->visitCast(I, SrcAbsV, SrcFlag, IsAllSigned);
	  else{
	    New = AbsV->clone();
	    New->makeTop();	      
	  }
	}
	break;
      default: 
#ifdef  WARNINGS
	dbgs() << "Warning: transfer function not implemented: " << I << "\n"; 
#endif  /* WARNINGS */
	assert(New == NULL);
	New = AbsV->clone();
	New->makeTop();
	NumOfSkippedIns++;
	break;
      } // end switch
      assert(New && "ERROR: something wrong during the transfer function ");
      PRINTCALLER("visitInst");
      // We do not delete New since it will be stored in a map
      // manipulated by updateState. Instead, updateState will free
      // the old value if it is replaced with New.
      updateState(I,New);
    }
  } 
}

// Function calls

/// Conservative assumptions if the code of the called function will
/// not be analyzed.
void FixpointSSI::
FunctionWithoutCode(CallInst *CInst, Function * Callee, Instruction *I){
  
  // Make top the return value if it's trackable by the analysis
  if (!I->getType()->isVoidTy()) {
    if (isTrackedCondFlag(I)){
      TBool * LHSFlag = TrackedCondFlags[I];    
      assert(LHSFlag && "ERROR: flag not found in TrackedCondFlags");
      LHSFlag->makeMaybe();
      DEBUG(dbgs() << "\tMaking the return value maybe: ");
      DEBUG(LHSFlag->print(dbgs()));
      DEBUG(dbgs() << "\n");
    }
    else{
      if (AbstractValue * LHS = ValueState[I]){
	DEBUG(dbgs() << "\tMaking the return value top: ");
	LHS->makeTop();
	DEBUG(LHS->print(dbgs()));
	DEBUG(dbgs() << "\n");
      }
    }
  }  
  
  if (Callee){
    // Make top all global variables that may be touched by the
    // function (CInst).
    for (SmallPtrSet<GlobalVariable*, 64>::iterator 
	   I = TrackedGlobals.begin(), E = TrackedGlobals.end();
	 I != E; ++I){    
      GlobalVariable *Gv = *I;
      AliasAnalysis::ModRefResult IsModRef = 
	AA->getModRefInfo(CInst,Gv,AliasAnalysis::UnknownSize);			
      if ( (IsModRef ==  AliasAnalysis::Mod) ||
	   (IsModRef ==  AliasAnalysis::ModRef) ){ 	
	if (TrackedGlobals.count(Gv)){
	  if (isTrackedCondFlag(Gv)){
	    TBool * GvFlag = TrackedCondFlags[Gv];    
	    assert(GvFlag && "ERROR: flag not found in TrackedCondFlags");
	    GvFlag->makeMaybe();
	    DEBUG(dbgs() <<"\tGlobal Boolean flag " << Gv->getName() 
		  << " may be modified by " 
		  << Callee->getName() <<".\n");
	  }
	  else{
	    AbstractValue * AbsGv = ValueState.lookup(Gv);
	    assert(AbsGv && "ERROR: entry not found in ValueState");
	    AbsGv->makeTop();
	    DEBUG(dbgs() <<"\tGlobal variable " << Gv->getName() 
		  << " may be modified by " 
		  << Callee->getName() <<".\n");
	  }
	}
      }
    }
  }
}

/// Since the analysis is intraprocedural we don't analysis the
/// callee.  We just consider the most pessimistic assumptions about
/// the callee: top for the return value and anything memory location
/// may-touched by the callee.
void FixpointSSI::visitCallInst(CallInst &CI) { 

  CallSite *CS   = new CallSite(&CI); 
  Function *F    = CS->getCalledFunction();
  Instruction *I = CS->getInstruction();

  DEBUG(dbgs() << "Function call " << *I << "\n");	      
  FunctionWithoutCode(&CI,F,I);		       
  delete CS;
}

/// Do nothing.
void FixpointSSI::visitReturnInst(ReturnInst &I){ 
  return;
}

/// Inform the analysis that it should track loads and stores to the
/// specified global variable if it can and it gives an initial
/// abstract value for each global variable. Note we following C
/// semantics we assign 0 to all uninitialized integer scalar global
/// variables.
void FixpointSSI::addTrackedGlobalVariables(Module *M) {
  /// Keep track only integer scalar global variables whose addresses
  /// have not been taken. In LLVM, if the address has not been taken
  /// then they memory object still has its def-use chains.
  for (Module::global_iterator 
	 Gv = M->global_begin(), E = M->global_end(); Gv != E; ++Gv){ 
    if (!Utilities::AddressIsTaken(Gv) && Gv->getType()->isPointerTy() 
	&& Gv->getType()->getContainedType(0)->isIntegerTy()) {
      DEBUG(printValueInfo(Gv,NULL));
      // Initialize the global variable
      if (Gv->hasInitializer()){
	if (ConstantInt * GvInitVal  = 
	    dyn_cast<ConstantInt>(Gv->getInitializer())){
	  if (isCondFlag(Gv)){
	    DEBUG(dbgs() << "\trecording a Boolean flag for global:" 
		  << Gv->getName() << "\n");
	    // FIXME: we ignore the initialized value and assume "maybe"
	      TrackedCondFlags.insert(std::make_pair(&*Gv, new TBool()));
	  }
	  else	
	      ValueState.insert(std::make_pair(&*Gv,
					       initAbsValIntConstant(Gv,GvInitVal)));
	}
      }
      else{
	if (isCondFlag(Gv)){
	  DEBUG(dbgs() << "\trecording a Boolean flag for global:" 
		<< Gv->getName() << "\n");
	  TBool * GvFlag = new TBool();
	  GvFlag->makeFalse();	      
	      TrackedCondFlags.insert(std::make_pair(&*Gv,GvFlag));	      
	}
	else{
	  ConstantInt * Zero = 
	    cast<ConstantInt>(ConstantInt::
			      get(Gv->getType()->getContainedType(0),
				  0, IsAllSigned));
	  ValueState.insert(std::make_pair(&*Gv,initAbsValIntConstant(Gv,Zero)));
	}
	}
      TrackedGlobals.insert(Gv);
    }    
  }
}


/// Here we keep track of global variables but we always initialize
/// with top so that each function is analyzed with correct
/// assumption.
void FixpointSSI::addTrackedGlobalVariablesPessimistically(Module *M) {
  /// Keep track only integer scalar global variables whose addresses
  /// have not been taken. In LLVM, if the address has not been taken
  /// then they memory object still has its def-use chains.

  for (Module::global_iterator Gv = M->global_begin(), E = M->global_end(); Gv != E; ++Gv){ 
    if (!Utilities::AddressIsTaken(Gv) && Gv->getType()->isPointerTy() &&
	Gv->getType()->getContainedType(0)->isIntegerTy()) {
      DEBUG(printValueInfo(Gv,NULL));
      // Initialize the global variable
      if (isCondFlag(Gv)){
	DEBUG(dbgs() << "\trecording a Boolean flag for global:" << Gv->getName() << "\n");
	  TrackedCondFlags.insert(std::make_pair(&*Gv,new TBool()));	      
      }
      else
	ValueState.insert(std::make_pair(&*Gv,initAbsValTop(Gv)));
      TrackedGlobals.insert(Gv);
    }    
  }
}

/// The store instruction is special since the destination is a
/// pointer which is not in SSA. We perform weak updates and also very
/// importantly, notify widening points about the change.
void FixpointSSI::visitStoreInst(StoreInst &I){
  // We care only about store related to tracked global variables
  
  Value *ptrOper = I.getPointerOperand();
  AbstractValue *checkZAbsValue = Lookup(ptrOper, false);
  
  if(checkZAbsValue && checkZAbsValue->hasNoZero()) {
    if(checkZAbsValue->getValueID() == 1) {
       // HERE Wrapped range is non-zero
       dbgs() << "Wrapped Range non-zero for:" << I << "\n";
    }
    if(checkZAbsValue->getValueID() == 2) {
        dbgs() << "Strided Range non-zero for:" << I << "\n";
    }
  }
  
  
  if (GlobalVariable *Gv = dyn_cast<GlobalVariable>(I.getPointerOperand())){
    if (TrackedGlobals.count(Gv)){
      // Special case if a Boolean Flag
      if (isTrackedCondFlag(Gv)){
	TBool * MemAddFlag = TrackedCondFlags[I.getPointerOperand()];    
	assert(MemAddFlag && "Memory location not mapped to a Boolean flag");
	DEBUG(dbgs() << "Memory store " << I << "\n");	  
	if (isTrackedCondFlag(I.getValueOperand())){
	  TBool * FlagToStore = TrackedCondFlags[I.getValueOperand()];
	  // weak update using disjunction
	  MemAddFlag->Or(MemAddFlag,FlagToStore);
	}
	else
	  MemAddFlag->makeMaybe();

	DEBUG(dbgs() <<"\t[RESULT] ");
	DEBUG(MemAddFlag->print(dbgs()));
	DEBUG(dbgs() <<"\n");      
	return;
      }
      AbstractValue * MemAddr = Lookup(I.getPointerOperand(), true);
      assert(MemAddr && "Memory location is not mapped in ValueState");	
      DEBUG(dbgs() << "Memory store " << I << "\n");	  
      // Weak update
      MemAddr->join(Lookup(I.getValueOperand(), true));	
      DEBUG(dbgs() <<"\t[RESULT] ");
      DEBUG(MemAddr->print(dbgs()));
      DEBUG(dbgs() <<"\n");      
      
      // Notify widening points about new change. 
      // FIXME: In fact we could test here if there is actually a
      // change. Otherwise, we don't need to notify anybody.
      // FIXME: maybe also other load instructions which postdominate I?
      for (Value::use_iterator UI = I.getPointerOperand()->use_begin(), 
	     E = I.getPointerOperand()->use_end(); UI != E; ++UI) {	  
	Instruction *U = cast<Instruction>(*UI);
	if (BBExecutable.count(U->getParent())){
	  if (WideningPoints.count(U)){
	      DEBUG(dbgs() << "***Added into I-WL: " << *U << "\n");
	      visitInst(*U);
	  }
	}
      }
      return;
    }
  }
  DEBUG(dbgs() << "Ignored memory store " << I << "\n");	  
}

// To avoid problems during narrowing 
void ResetAbstractValue(AbstractValue * V){
  V->makeBot();
}

/// Load the abstract value from the memory pointer to the lhs of the
/// instruction and insert into the worklist all its users. We care
/// only about tracked global variables.
void FixpointSSI::visitLoadInst(LoadInst &I){

  Value *ptrOper = I.getPointerOperand();
  AbstractValue *checkZAbsValue = Lookup(ptrOper, false);
  
  if(checkZAbsValue && checkZAbsValue->hasNoZero()) {
      if(checkZAbsValue->getValueID() == 1) {
           // HERE Wrapped range is non-zero
            dbgs() << "Wrapped Range non-zero for:" << I << "\n";
      }
      if(checkZAbsValue->getValueID() == 2) {
            dbgs() << "Strided Range non-zero for:" << I << "\n";
      }

  }

  /// We care only about store related to tracked global variables
  if (GlobalVariable *Gv = dyn_cast<GlobalVariable>(I.getPointerOperand())){
    if (TrackedGlobals.count(Gv)){
      // Special case if a Boolean Flag
      if (isTrackedCondFlag(Gv)){
	TBool * LHSFlag = new TBool(*TrackedCondFlags[&I]);    
	assert(LHSFlag && "Memory location not mapped to a Boolean flag");
	if (isTrackedCondFlag(I.getPointerOperand())){
	  TBool * MemAddFlag = TrackedCondFlags[I.getPointerOperand()];
	  LHSFlag->makeTrue();
	  LHSFlag->And(LHSFlag,MemAddFlag);
	}
	else
	  LHSFlag->makeMaybe();
	// We do not delete LHSFlag since it will be stored in a map
	// manipulated by updateCondFlag. Instead, updateCondFlag will
	// free the old value if it is replaced with LHSFlag.
	updateCondFlag(I,LHSFlag);
	DEBUG(dbgs() << "\t[RESULT] ");
	DEBUG(LHSFlag->print(dbgs()));
	DEBUG(dbgs() << "\n");            
	return;
      }
     
      AbstractValue * LHS = Lookup(&I, false);
      if (!LHS) return;
      DEBUG(dbgs() << "Memory Load " << I << "\n");	  
      // Clone LHS in order to compare with old value in updateState
      AbstractValue * NewLHS = LHS->clone();        
      // Assign from memory to lhs
      ResetAbstractValue(NewLHS);
      NewLHS->join(Lookup(I.getPointerOperand(), true));      
      DEBUG(dbgs() << "\t[RESULT] ");
      DEBUG(NewLHS->print(dbgs()));
      DEBUG(dbgs() << "\n");                  
      // Compare if it loads a new value and then add I into the
      // worklist
      PRINTCALLER("visitLoadInst");
      // We do not delete NewLHS since it will be stored in a map
      // manipulated by updateState. Instead, updateState will free
      // the old value if it is replaced with NewLHS.
      updateState(I,NewLHS);
      return;
    }
  } 
  DEBUG(dbgs() << "Ignored memory load " << I << "\n");	  
  AbstractValue * LHS = Lookup(&I, false);
  // No need to call updateState since it's top from the beginning.
  if (LHS) LHS->makeTop();
}

// Execution of sigma nodes 

/// Helper to add the map from V to Sigma in
/// TrackedValuesUsedSigmaNode.
void insertTrackedValuesUsedSigmaNode(SigmaUsersTy &TrackedValuesUsedSigmaNode, 
				      Value *V, Value *LHSSigma){
  
  if (!isa<ConstantInt>(V)){
    DEBUG(dbgs() << "Adding " << V->getName() << " -> " << LHSSigma->getName() << "\n");
    if (SmallValueSet * SigmaSet = TrackedValuesUsedSigmaNode[V]){
      SigmaSet->insert(LHSSigma);
    }
    else{
      SmallValueSet * NSigmaSet = new SmallValueSet;
      NSigmaSet->insert(LHSSigma);
      TrackedValuesUsedSigmaNode[V] = NSigmaSet; 
    }
  }
}

/// Add the entry LHSSigma --> (Op1 'pred' Op2) 
/// Pre: there is no entry for LHSSigma.
void genConstraint(unsigned pred, Value *Op1, Value *Op2,
		   SigmaFiltersTy &filters,
		   Value * LHSSigma,
		   SigmaUsersTy &TrackedValuesUsedSigmaNode){
  
  BinaryConstraintPtr C(new BinaryConstraint(pred,Op1,Op2));
  // Sanity check 
  // SigmaFiltersTy::iterator It = filters.find(LHSSigma);
  // assert(It == filters.end());
  filters.insert(std::make_pair(LHSSigma, C));
  DEBUG(dbgs() << "\t"; C->print(); dbgs() << "\n");

  // Key step for correctness of the fixpoint.
  insertTrackedValuesUsedSigmaNode(TrackedValuesUsedSigmaNode,Op1, LHSSigma);					          
  insertTrackedValuesUsedSigmaNode(TrackedValuesUsedSigmaNode,Op2, LHSSigma);					          
}


// /// Generate the constraint Op1 'pred' Op2 and record that the
// /// constraint is a filter for both Op1 and Op2.
// void genConstraint(unsigned pred, Value *Op1, Value *Op2,
// 		   FiltersTy    &filters,
// 		   Value * LHSSigma,
// 		   SigmaUsersTy &TrackedValuesUsedSigmaNode){
  
//   BinaryConstraintPtr C(new BinaryConstraint(pred,Op1,Op2));
//   if (!C->isConstantOperand(0)){
//     FiltersTy::iterator It = filters.find(Op1);
//     if (It != filters.end()){
//       BinaryConstraintSetTy *Rhs  = It->second;
//       assert(Rhs);
//       Rhs->insert(C);
//       filters[Op1]=Rhs;
//       DEBUG(dbgs() << "\t" ; C->print(); dbgs() << "\n");
//     }
//     else{
//       BinaryConstraintSetTy * Rhs = new BinaryConstraintSetTy();
//       Rhs->insert(C);
//       filters.insert(std::make_pair(Op1, Rhs));
//       DEBUG(dbgs() << "\t"; C->print(); dbgs() << "\n");
//     }
//   }

//   if (!C->isConstantOperand(1)){
//     FiltersTy::iterator It = filters.find(Op2);
//     if (It != filters.end()){
//       BinaryConstraintSetTy *Rhs = It->second;
//       assert(Rhs);
//       Rhs->insert(C);
//       filters[Op2]=Rhs;
//       DEBUG(dbgs() << "\t"; C->print(); dbgs() << "\n");
//     }
//     else{
//       BinaryConstraintSetTy *Rhs = new BinaryConstraintSetTy();
// 	Rhs->insert(C);
// 	filters.insert(std::make_pair(Op2, Rhs));
// 	DEBUG(dbgs() << "\t"; C->print(); dbgs() << "\n");
      
//     }
//   }
//   // Key step for correctness of the fixpoint.
//   insertTrackedValuesUsedSigmaNode(TrackedValuesUsedSigmaNode,Op1, LHSSigma);
//   insertTrackedValuesUsedSigmaNode(TrackedValuesUsedSigmaNode,Op2, LHSSigma);
// }

void visitInstrToFilter(Value * LHSSigma, Value * RHSSigma, 
			BranchInst *BI, BasicBlock *SigmaBB, ICmpInst* CI, 
			SigmaFiltersTy    &filters,
			SigmaUsersTy &TrackedValuesUsedSigmaNode){

  if (CI->getOperand(0) == RHSSigma || CI->getOperand(1) == RHSSigma){
    assert((BI->getSuccessor(0) == SigmaBB || BI->getSuccessor(1) == SigmaBB )
	   && "This should not happen");

    // Figure out whether it is a "then" or "else" block.
    if (BI->getSuccessor(0) == SigmaBB)
      genConstraint(CI->getSignedPredicate(), 
		    CI->getOperand(0), CI->getOperand(1), 
		    filters, LHSSigma, TrackedValuesUsedSigmaNode);  
    else 
      genConstraint(CI->getInversePredicate(CI->getSignedPredicate()), 
		    CI->getOperand(0), CI->getOperand(1), 
		    filters, LHSSigma, TrackedValuesUsedSigmaNode);
  }
  else{
    // Case to improve
#ifdef WARNINGS
    dbgs() << "Searching for " << RHSSigma->getName() << "in: \n";
    dbgs() << *(BI->getParent()) << "\n";
    dbgs() << *(SigmaBB) << "\n";
#endif 
    return; // no filtering here!
  }
}

/// Key method for precision: refine RHSSigma using information from
/// the branch condition BI.
void FixpointSSI::generateFilters(Value *LHSSigma, Value *RHSSigma, 
				  BranchInst *BI, BasicBlock *SigmaBB
				  /*, FiltersTy &filters*/){
  unsigned width;
  DEBUG(dbgs() << "Generating filters for " << SigmaBB->getName() << ":" 
	       << RHSSigma->getName() << ":\n");
  if (ICmpInst * CI = dyn_cast<ICmpInst>(BI->getCondition())){
    // If it is not of the type and width that we can track then
    // no bother
    if (Utilities::getIntegerWidth(CI->getType(),width))
      visitInstrToFilter(LHSSigma, RHSSigma, BI, SigmaBB, CI, 
			 SigmaFilters, TrackedValuesUsedSigmaNode);
  }

#ifdef  WARNINGS
  else if (SelectInst * SI = dyn_cast<SelectInst>(BI->getCondition())){
    // if (Utilities::getIntegerWidth(SI->getType(),width))
    dbgs() << "Warning: no filter generated for " << *SI << "\n";
    //visitInstrToFilter(RHSSigma, BI, SI);
  }
  else if (IsBooleanLogicalOperator(dyn_cast<Instruction>(BI->getCondition()))){
    Instruction * BoolI = dyn_cast<Instruction>(BI->getCondition());
    dbgs() << "Warning: no filter generated for " << *BoolI << "\n";
    //visitInstrToFilter(RHSSigma, BI, cast<Instruction>(BI->getCondition()),
    //	       TrackedCondFlags);
  }
  else if (PHINode *PHI = dyn_cast<PHINode>(BI->getCondition())){
    dbgs() << "Warning: no filter generated for " << *PHI << "\n";
    // For instance, we can have instructions like:
    // bb1:
    //   tmp2.pre-phi = phi i1 [false, %bb3], [%tmp2.pre, %bb]
    //   br i1, %tmp2.pre-phi, label %bb6, label %bb3
    // bb3: 
    //   ...
    //   br label %bb1
    //
    // This is coming from code like while(*){ } so there is not
    // much to do here. I think we do not lose too much if we
    // leave uncovered this case.
  }
  else if (FCmpInst * FCI = dyn_cast<FCmpInst>(BI->getCondition())){
    // We do not reason at all about floating numbers even if they
    // can become integer after some casting.
    dbgs() << "Warning: no filter generated for " << *FCI << "\n";
  }
  else if (LoadInst *LI = dyn_cast<LoadInst>(BI->getCondition())){
    dbgs() << "Warning: no filter generated for " << *LI << "\n";
  }
  else{
    dbgs() << "Uncovered case by visitInstrToFilter: \n\t";
    dbgs() <<  *(BI->getCondition()) << "\n";
    dbgs() << "We may avoid the analysis losing precision!\n";
    // Temporary raise exception to be aware of the unsupported case.
    llvm_unreachable("Unsupported case")
  }
#endif  /*WARNINGS*/
}


/// For reducing the number of cases, normalize the constraint with
/// respect to V. V appears always as the first argument in F.
void normalizeConstraint(BinaryConstraintPtr & FPtr, Value *V){
  bool isOp1Constant = isa<ConstantInt>(FPtr.get()->getOperand(0));
  bool isOp2Constant = isa<ConstantInt>(FPtr.get()->getOperand(1));
  assert(!(isOp1Constant && isOp2Constant));
  if (isOp1Constant && !isOp2Constant){
    // We swap operands to have first operand the variable and the
    // second the constant
    FPtr.get()->swap();
  }    
  else if (!isOp1Constant && !isOp2Constant){
    assert( (FPtr.get()->getOperand(0) == V) || 
	    (FPtr.get()->getOperand(1) == V));
    if (FPtr.get()->getOperand(1) == V){
      // We swap operands to have first operand the variable that we
      // want to refine.
      FPtr.get()->swap();
    }
  }    
}

/// Execute the filters generated for RHSSigma and store the result in
/// LHSSigma.
bool FixpointSSI::evalFilter(AbstractValue * &LHSSigma, Value *RHSSigma){
  bool FilteredDone=false;
  SigmaFiltersTy::iterator I = SigmaFilters.find(LHSSigma->getValue());
  if (I != SigmaFilters.end()){
    BinaryConstraintPtr C = (*I).second;
    DEBUG(dbgs() << "Evaluating filter constraints: "; C.get()->print();  dbgs() << "\n");
    normalizeConstraint(C,RHSSigma);
    DEBUG(dbgs() << "After normalization          : "; C.get()->print();  dbgs() << "\n");
    // After normalization we know that Op1 is the default value for
    // LHS which we hope to refine by using Op2.
    AbstractValue * Op1 = Lookup(C.get()->getOperand(0), true);
    AbstractValue * Op2 = Lookup(C.get()->getOperand(1), true);
    
    // This is too restrictive: If Op1 is already top then we do not
    // bother.
    // if (Op1->IsTop()){ LHSSigma->makeTop(); break; } 
    
    // Here we cannot filter since Op2 is top.
    if (Op2->IsTop()) return false;
    if (Op2->isBot()) return false;
    
    unsigned pred       = C.get()->getPred();
    DEBUG( LHSSigma->print(dbgs()); dbgs() << "\n");
    DEBUG( Op1->print(dbgs()); dbgs() << "\n");
    DEBUG( Op2->print(dbgs()); dbgs() << "\n");     

    // Do not remember why I cloned here but it does not make sense.
    // LHSSigma->filterSigma(pred, Op1->clone(), Op2->clone());
    LHSSigma->filterSigma(pred, Op1, Op2);

    DEBUG( LHSSigma->print(dbgs()); dbgs() << "\n");
    FilteredDone=true;
  }
  return FilteredDone;
}



// /// Execute the filters generated for RHSSigma and store the result in
// /// LHSSigma.
// bool FixpointSSI::evalFilter(AbstractValue * &LHSSigma, Value *RHSSigma, 
// 			     const FiltersTy filters){
//   bool FilteredDone=false;
//   FiltersTy::const_iterator I = filters.find(RHSSigma);
//   if (I != filters.end()){
//     BinaryConstraintSetTy * Rhs = I->second;

//     assert(Rhs->size() < 2);

//     for (BinaryConstraintSetTy::iterator II=Rhs->begin(), EE=Rhs->end(); II!=EE; ++II){
//       BinaryConstraintPtr C = *II;
//       DEBUG(dbgs() << "Evaluating filter constraints: "; C.get()->print();  dbgs() << "\n");
//       normalizeConstraint(C,RHSSigma);
//       DEBUG(dbgs() << "After normalization          : "; C.get()->print();  dbgs() << "\n");
//       AbstractValue * Op1 = Lookup(C.get()->getOperand(0), true);
//       AbstractValue * Op2 = Lookup(C.get()->getOperand(1), true);

//       // After normalization we know that Op1 is the default value for
//       // LHS which we hope to refine by using Op2. 
//       // (This is too restrictive: If Op1 is already top then we do not
//       // bother)
//       //if (Op1->IsTop()){ LHSSigma->makeTop(); break; } 

//       // Here we cannot filter since Op2 is top.
//       if (Op2->IsTop()) return false;
//       if (Op2->isBot()) return false;

//       unsigned pred       = C.get()->getPred();
//       DEBUG( LHSSigma->print(dbgs()); dbgs() << "\n");
//       DEBUG( Op1->print(dbgs()); dbgs() << "\n");
//       DEBUG( Op2->print(dbgs()); dbgs() << "\n");     
//       LHSSigma->filterSigma(pred, Op1->clone(), Op2->clone());
//       DEBUG( LHSSigma->print(dbgs()); dbgs() << "\n");
//       FilteredDone=true;
//     }
//   }
//   return FilteredDone;
// }

/// Simply assign RHSSigma to LHSSigma.
void FixpointSSI::visitSigmaNode(AbstractValue *LHSSigma, Value * RHSSigma){
  // In programs like 176.gcc we have things like:
  //  %.01.i = phi i32 [ ptrtoint (double* getelementptr inbounds 
  //                     (%struct.fooalign* null, i32 0, i32 1) to i32), 
  //                     %bb3.i ]
  // Thus, we can raise an exception if RHSSigma is not found.

  ResetAbstractValue(LHSSigma);
  if (AbstractValue *AbsVal = Lookup(RHSSigma,false))
    LHSSigma->join(AbsVal);
  else
    LHSSigma->makeTop();
}

// Execute a sigma node in two steps. The execution consists of
// assigning RHSSigma to LHSSigma. Additionally, knowledge from BI is
// used to improve LHSSigma. First it generates any filter that it can
// be inferred from the branch condition. Second, it actually executes
// the filter.
void FixpointSSI::visitSigmaNode(AbstractValue *LHSSigma, Value * RHSSigma,
				 BasicBlock *SigmaBB, BranchInst * BI){				 
  // FiltersTy filters;
  // generateFilters(LHSSigma->getValue(), RHSSigma, BI, SigmaBB, filters);

  SigmaFiltersTy::iterator I = SigmaFilters.find(LHSSigma->getValue());
  if (I == SigmaFilters.end())
    generateFilters(LHSSigma->getValue(), RHSSigma, BI, SigmaBB);

  
  if (!evalFilter(LHSSigma, RHSSigma /*, filters*/)){
    // Assign RHSSigma to LHSSigma
    ResetAbstractValue(LHSSigma);
    // LHSSigma->join(Lookup(RHSSigma,true));
    if (AbstractValue * AbsVal = Lookup(RHSSigma,false))
      LHSSigma->join(AbsVal);
    else
      LHSSigma->makeTop();

  }
}


/// Special case if the underlying domain is a non-lattice.  The
/// implementation of visitPHINode assumes that the underlying
/// abstract domain is associative. That is, join(join(x,y)),z) =
/// join(x, join(y,z)). However, non-lattice joins are not
/// associative. In that case, we prefer not to join directly all the
/// incoming values since different orders although sound may give
/// different levels of precision. Instead, we just collect all
/// incoming values and put them into a vector which is passed
/// directly to the non-lattice domain which knows how to deal with
/// this lack of associativity.
void FixpointSSI::visitPHINode(AbstractValue *&AbsValNew, PHINode &PN){

  bool must_be_top=false;
  std::vector<AbstractValue*> AbsIncVals;
  
  for (unsigned i=0, num_vals=PN.getNumIncomingValues(); i != num_vals;i++) {
    if (isEdgeFeasible(PN.getIncomingBlock(i), PN.getParent()) && 
	(PN.getIncomingValue(i)->getValueID() != Value::UndefValueVal)){				   
      AbstractValue * AbsIncVal = Lookup(PN.getIncomingValue(i),false);
      if (!AbsIncVal){
	must_be_top = true;
	break;
      }
      else
	AbsIncVals.push_back(AbsIncVal);
    }
  } // end for
  if (must_be_top)
    AbsValNew->makeTop();
  else
    AbsValNew->GeneralizedJoin(AbsIncVals);
  
  PRINTCALLER("visitPHI");
  updateState(PN,AbsValNew);
  DEBUG(dbgs() << "\t[RESULT] ");
  DEBUG(AbsValNew->print(dbgs()));
  DEBUG(dbgs() << "\n");        
}

/// This method covers actually two different instructions. A sigma
/// node is represented as a phi node but with a single incoming
/// block.
///
/// If a sigma node then it attempts at improving the precision of the
/// value by restricting it using information from the conditional
/// branch of the incoming block of the sigma node.
///
/// If a phi node then it merges the values only from feasible
/// predecessors.

void FixpointSSI::visitPHINode(PHINode &PN) {
  if (Value *V = dyn_cast<Value>(&PN)){
    if (AbstractValue * AbsVal = Lookup(V, false)){       
      if (PN.getNumIncomingValues() == 1){
	// Sigma node is represented as a phi node with exactly one
	// incoming value.
	DEBUG(dbgs() << "Sigma node " << PN << "\n");
	AbstractValue * NewAbsVal = AbsVal->clone();  	
	if (TerminatorInst * TI  = PN.getIncomingBlock(0)->getTerminator()){
	  if (BranchInst * BI  = dyn_cast<BranchInst>(TI)){
	    //assert(BI->isConditional());
	    if (BI->isConditional())
	      visitSigmaNode(NewAbsVal, PN.getIncomingValue(0), PN.getParent(), BI);
	    else
	      visitSigmaNode(NewAbsVal, PN.getIncomingValue(0));
	  }
	}
	PRINTCALLER("visitSigmaNode");
	// We do not delete NewAbsVal since it will be stored in a map
	// manipulated by updateState. Instead, updateState will free
	// the old value if it is replaced with NewAbsVal.
	updateState(PN,NewAbsVal);

	DEBUG(dbgs() << "\t[RESULT] ");
	DEBUG(NewAbsVal->print(dbgs()));
	DEBUG(dbgs() << "\n");        
      } 
      else{
	// PHI node
	AbstractValue *AbsValNew = AbsVal->clone();
	//ResetAbstractValue(AbsValNew);
	AbsValNew->makeBot();

	DEBUG(dbgs() << "PHI node " << PN << "\n");

	// If the abstract domain is not a lattice then we call go
	// GeneralizedJoin, a special version, for joining multiple
	// abstract values. If the abstract domain is a lattice we
	// don't need such a specialized method since we can use the
	// binary join repeatedly without losing precision. For a
	// non-lattice domain is not the case (see our SAS'13 paper).
	if (!(AbsValNew->isLattice()))
	  visitPHINode(AbsValNew,PN);
	else{	  
	  for (unsigned i=0, num_vals=PN.getNumIncomingValues(); i != num_vals;i++) {
	    // if (!isEdgeFeasible(PN.getIncomingBlock(i), PN.getParent()))
	    //   dbgs() << PN.getIncomingBlock(i)->getName()
	    // 	     << " --> " << PN.getParent()->getName()  << " IS UNREACHABLE\n";
	    // else{
	    //   dbgs() << PN.getIncomingBlock(i)->getName() 
	    // 	     << " --> " << PN.getParent()->getName()  << " IS REACHABLE\n";
	    // }
	    if (isEdgeFeasible(PN.getIncomingBlock(i), PN.getParent()) && 
		(PN.getIncomingValue(i)->getValueID() != Value::UndefValueVal)){				   
	      /// Merging values: since join can only lose precision
	      /// we stop if we already reach top.
	      
	      if (AbsValNew->IsTop()){ 
		DEBUG(dbgs() << "Skipped " << *(PN.getIncomingValue(i)) 
		             << " because already top!\n");
		break;	       
	      }
	      AbstractValue * AbsIncVal = Lookup(PN.getIncomingValue(i),false);
	      DEBUG(dbgs() << "Merging " << *(PN.getIncomingValue(i)) << "\n");
	      if (!AbsIncVal){
		AbsValNew->makeTop();
		DEBUG(dbgs() << "Could not find " << *(PN.getIncomingValue(i)) 
		             << " in the lookup table. \n");
		break;
	      }
	      else
		AbsValNew->join(AbsIncVal);
	    }
	  } // end for
	  PRINTCALLER("visitPHI");
	  // We do not delete NewAbsVal since it will be stored in a map
	  // manipulated by updateState. Instead, updateState will free
	  // the old value if it is replaced with NewAbsVal.
	  updateState(PN,AbsValNew);
	  DEBUG(dbgs() << "\t[RESULT] ");
	  DEBUG(AbsValNew->print(dbgs()));
	  DEBUG(dbgs() << "\n");        
	} 
      }
    }
  }
}

/// Join the abstract values of the two operands and store it in the
/// lhs. If it is known whether the condition is true or false the
/// join can be refined. We have a separate treatment if the operands
/// are Boolean flags.
void FixpointSSI::visitSelectInst(SelectInst &Ins){
  DEBUG(dbgs() << "Select Instruction " << Ins << "\n");

  // Special case: SelectInst involves only Boolean flags
  if  (TrackedCondFlags.lookup(&Ins)){     
    // Make sure we make a copy here
    TBool *LHS = new TBool(*TrackedCondFlags.lookup(&Ins));    
    if  (TBool * Cond  = TrackedCondFlags.lookup(Ins.getCondition())){
      if (TBool * True  = getTBoolfromValue(Ins.getTrueValue())){
	if (TBool * False = getTBoolfromValue(Ins.getFalseValue())){     
	  if (Cond->isTrue()){
	    LHS->makeTrue();
	    LHS->And(LHS,True);
	  }
	  else{
	    if (Cond->isFalse()){
	      LHS->makeTrue();
	      LHS->And(LHS,False);
	    }
	    else 
	      LHS->Or(True,False);
	  }
	  goto BOOL_END;	  
	}
      }
    }
    // Some of the operands is not trackable but LHS is
    LHS->makeMaybe();
  BOOL_END:
    // We do not delete LHS since it will be stored in a map
    // manipulated by updateCondFlag. Instead, updateCondFlag will
    // free the old value if it is replaced with LHS.
    updateCondFlag(Ins,LHS);
    DEBUG(dbgs() << "\t[RESULT] ");
    DEBUG(LHS->print(dbgs()));
    DEBUG(dbgs() << "\n");        
    return;
  }

  // General case: all the operands are AbstractValue objects

  // Important: clone here to be able to compare old value later.
  AbstractValue * OldLHS = Lookup(&Ins, false);
  if (!OldLHS) return;   
  AbstractValue * LHS   = OldLHS->clone();  
  AbstractValue * True  = Lookup(Ins.getTrueValue(), false);
  AbstractValue * False = Lookup(Ins.getFalseValue(), false);

  // FIXME: we can have instructions like:
  // %tmp128 = select i1 %tmp126, i32 -1, i32 %tmp127
  // where %tmp127 is untrackable.
  if (!True || !False){
    LHS->makeTop();
    goto END_GENERAL;
  }

  ResetAbstractValue(LHS);  
  if (!isTrackedCondFlag(Ins.getCondition())){
    // The condition is not trackable as a Boolean Flag so we join
    // both
    LHS->join(True);
    LHS->join(False);    
  }
  else{   
      TBool * Cond = TrackedCondFlags.lookup(Ins.getCondition());
      if (Cond->isTrue())    // must be true
	LHS->join(True);
      else{
	if (Cond->isFalse()) // must be false
	  LHS->join(False);
	else{                // maybe
	  LHS->join(True);
	  LHS->join(False);	  
	}
      }
  }
 END_GENERAL:
  PRINTCALLER("visitSelectInst");

  // We do not delete LHS since it will be stored in a map
  // manipulated by updateState. Instead, updateState will free
  // the old value if it is replaced with LHS.
  updateState(Ins,LHS);
  DEBUG(dbgs() << "\t[RESULT] ");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");          
}


// visitTerminatorInst - Mark all possible executable transitions from
// the terminator.  We cover for now IndirectBrInst (we always add all
// successors), SwitchInst, and BranchInst. This procedure is vital to
// improve accuracy of the analysis.
void FixpointSSI::visitTerminatorInst(TerminatorInst &TI){

  assert(! (isa<SwitchInst>(&TI)) && 
	 "The program should not have switch (-lowerswitch)");
  assert(! (isa<IndirectBrInst>(&TI)) && 
	 "The program should not have indirect branches");

  if (BranchInst * Branch = dyn_cast<BranchInst>(&TI)){
    if (Branch->isUnconditional()){
      DEBUG(dbgs() << "Unconditional branch: " << *Branch << "\n") ;
      assert(Branch->getNumSuccessors() == 1);
      markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(0));
      return;
    } // End Unconditional Branch

    DEBUG(dbgs() << "Conditional branch: " << *Branch << "\n") ;
    assert(Branch->getNumSuccessors() == 2);

    // Special cases if constants true or false
    if (isTrueConstant(Branch->getCondition())){
      DEBUG(dbgs() << "\tthe branch condition is MUST BE TRUE.\n") ;
      markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(0));
      return;
    }
    if (isFalseConstant(Branch->getCondition())){
      DEBUG(dbgs() << "\tthe branch condition is MUST BE FALSE.\n") ;		    
      markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(1));		
      return;
    }

    // We do not keep track of the flag so everything can happen
    if (!isTrackedCondFlag(Branch->getCondition())){
	DEBUG(dbgs() << "\tthe branch condition is MAY-TRUE/MAY-FALSE.\n") ;
	markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(0));
	markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(1));
	return;
    }    

    TBool * Cond = TrackedCondFlags.lookup(Branch->getCondition());    
    if (Cond->isBottom()){
      DEBUG(dbgs() << "\tthe branch condition is BOTTOM!\n") ;
      DEBUG(dbgs() << "\tthe successors are UNREACHABLE!\n") ;
      return;
    }

    if (Cond->isMaybe()){
      DEBUG(dbgs() << "\tthe branch condition is MAYBE TRUE OR FALSE.\n") ;
      markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(0));
      markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(1));
      return;
    }
    if (Cond->isTrue()){
      DEBUG(dbgs() << "\tthe branch condition is MUST BE TRUE.\n") ;
      markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(0));
      return;
    }
    if (Cond->isFalse()){
      DEBUG(dbgs() << "\tthe branch condition is MUST BE FALSE.\n") ;		    
      markEdgeExecutable(Branch->getParent(),Branch->getSuccessor(1));		
      return;
    }      
  } // End BranchInst

  // UnreachableInst
  if (isa<UnreachableInst>(&TI)){
    // FIXME: all the abstract values should be bottom!
    DEBUG(dbgs() << "Unreachable instruction. \n") ;
    return;
  }

  dbgs() << TI << "\n";
  llvm_unreachable("Found an unsupported terminator instruction.");
}

// Reduce the number of cases. After calling getPredicate and
// swap, only six cases: EQ, NEQ, SLE, ULE, ULT, and SLT
// 
// Important: for some reason if an instruction is swap it may disable
// some def-use chains. This causes to reach too early fixpoints
// (e.g., test-unbounded-loop-3.c). This weird behaviour is not
// documented so it's hard to see why. Our solution is to clone the
// instruction which we want to swap. However, we have to be careful
// since if we try to lookup in one of our tables using that cloned
// instruction the search will fail.
ICmpInst * normalizeCmpInst(ICmpInst &I){
  ICmpInst *II = cast<ICmpInst>(I.clone());
  switch (II->getPredicate()){
  case ICmpInst::ICMP_UGT:	
  case ICmpInst::ICMP_SGT:	
    II->swapOperands();
    break;
  case ICmpInst::ICMP_UGE:	
  case ICmpInst::ICMP_SGE:	
    II->swapOperands();
    break;
  default: 
    ;
  }
  return II;
}


void comparisonEqInst(TBool &LHS, 
		      AbstractValue *I1, AbstractValue *I2, 
		      bool meetIsBottom, unsigned OpCode){
  // Pre: this method cannot be called if V1 or V2 is bottom		      
  switch (OpCode){
  case ICmpInst::ICMP_EQ:
    if (!meetIsBottom){         // must be true or maybe
      if(I1->isGammaSingleton() && I1->isIdentical(I2))
	LHS.makeTrue();         // must be true
      else
	LHS.makeMaybe();
    }
    else                        // must be false
      LHS.makeFalse();  
    break;
  case ICmpInst::ICMP_NE:
    if (meetIsBottom){
      // LHS.makeMaybe();          // must be true
      // 13/05/2013: if intersection is empty I1 and I2 are for sure
      // not equal.
      LHS.makeTrue() ;
    }
    else{                       // must be false or maybe
      if(I1->isGammaSingleton() && I1->isIdentical(I2))
      	LHS.makeFalse();  
      else
	LHS.makeMaybe();
    }
    break;
    llvm_unreachable("ERROR: undefined argument in predEquality ");
  }
}

void comparisonSleInst(TBool &LHS, AbstractValue* V1, AbstractValue *V2){ 
  // Pre: this method cannot be called if V1 or V2 is bottom
  if (V1->comparisonSle(V2)){
    if (V2->comparisonSlt(V1))
      LHS.makeMaybe();   
    else
      LHS.makeTrue();   // must be true
  }
  else
    LHS.makeFalse();    // must be false
}

void comparisonSltInst(TBool &LHS, AbstractValue *V1, AbstractValue*V2){
  // Pre: this method cannot be called if V1 or V2 is bottom
  if (V1->comparisonSlt(V2)){
    if (V2->comparisonSle(V1))
      LHS.makeMaybe();   
    else
      LHS.makeTrue();   // must be true
  }
  else
    LHS.makeFalse();    // must be false
}

void  comparisonUleInst(TBool &LHS, AbstractValue* V1, AbstractValue *V2){ 
  if (V1->comparisonUle(V2)){
    if (V2->comparisonUlt(V1))  
      LHS.makeMaybe();   
    else LHS.makeTrue();   // must be true
  }
  else
    LHS.makeFalse();    // must be false
}

void  comparisonUltInst(TBool &LHS, AbstractValue *V1, AbstractValue*V2){
  if (V1->comparisonUlt(V2)){
    if (V2->comparisonUle(V1)) 
       LHS.makeMaybe();   
    else 
       LHS.makeTrue();   // must be true
  }
  else
    LHS.makeFalse();    // must be false
}

/// Wrapper to call the meet operation and returns true iff the meet
/// between the two abstract values is bottom.  The wrapper is needed
/// to make sure that the meet method is called by a non-constant
/// value.
bool IsMeetEmpty(AbstractValue *V1,AbstractValue* V2){
  if (V1->isConstant() && V2->isConstant())
    return (!V1->isIdentical(V2));
  else{
    if (!V1->isConstant()){
      AbstractValue *Meet = V1->clone();
      Meet->meet(V1,V2);
      bool result = Meet->isBot();
      delete Meet;
      return result;
    }
    else{      
      AbstractValue *Meet = V2->clone();
      Meet->meet(V1,V2);
      bool result = Meet->isBot();
      delete Meet;
      return result;
    }
  }
}

///  Execute a comparison instruction and store the result: "must
///  true", "must false", or "maybe" in the abstract value of the lhs
///  which must be a TBool object.
void FixpointSSI::visitComparisonInst(ICmpInst &I){

  DEBUG(dbgs() << "Comparison instruction: " << I << "\n");
  if (!isTrackedCondFlag(&I)) return;
  // May swap operands of I: don't do lookups using ClonedI as a base
  // pointer !!
  ICmpInst* ClonedI = normalizeCmpInst(I);    
  // Make sure we make a copy here
  TBool *LHS = new TBool(*TrackedCondFlags.lookup(&I));

  ///////////////////////////////////////////////////////////////////////////////
  // The operands of the ICmpInst could be actually anything. E.g.,
  // 
  // %tmp37 = icmp ult double* %table.0, getelementptr inbounds ([544
  // x double]* @decwin, i32 0, i32 528) 
  //
  // Here the operands are not in ValueState. Thus, we cannot raise an
  // assertion in that case. Instead, we just make "maybe" the lhs of
  // the instruction.
  ///////////////////////////////////////////////////////////////////////////////
  if (AbstractValue *Op1 = Lookup(ClonedI->getOperand(0), false)){
    if (AbstractValue *Op2 = Lookup(ClonedI->getOperand(1), false)){
      if (Op1->isBot() || Op2->isBot()){
	// LHS->makeBottom();
	// It is more conservative this:
	LHS->makeMaybe();
	goto END;
      }
      if (Op1->IsTop() || Op2->IsTop()){
	// Here is one of the operands is top we just say maybe.
	LHS->makeMaybe();
	goto END;
      }
      // Cloned has been already normalized (removed some cases)
      switch (ClonedI->getPredicate()){
      case ICmpInst::ICMP_EQ:
	comparisonEqInst(*LHS,Op1,Op2,IsMeetEmpty(Op1,Op2),ICmpInst::ICMP_EQ);
	break;
      case ICmpInst::ICMP_NE:
	comparisonEqInst(*LHS,Op1,Op2,IsMeetEmpty(Op1,Op2),ICmpInst::ICMP_NE);
	break;
      case ICmpInst::ICMP_ULE:	  
	comparisonUleInst(*LHS,Op1, Op2);
	break;
      case ICmpInst::ICMP_ULT:	  
	comparisonUltInst(*LHS,Op1, Op2);
	break;
      case ICmpInst::ICMP_SLE:	  
	comparisonSleInst(*LHS,Op1, Op2);
	break;
      case ICmpInst::ICMP_SLT:	  
	comparisonSltInst(*LHS,Op1, Op2);
	break;
      default:
	llvm_unreachable("ERROR: uncovered comparison operator");
      }  
      goto END;
    }
  }
  // If this point is reachable is because either V1 or v2 were not
  // found in ValueState.
  LHS->makeMaybe();

 END:  
  delete ClonedI;      
  DEBUG(dbgs() << "\t[RESULT]");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");          
  
  // We do not delete LHS since it will be stored in a map manipulated
  // by updateCondFlag. Instead, updateCondFlag will free the old
  // value if it is replaced with LHS.
  updateCondFlag(I,LHS);
}

///  Execute logical operations (and, or, xor) on 1-bit variables
///  (i.e., Boolean flag) using three-valued logic.
void FixpointSSI::visitBooleanLogicalInst(Instruction &I){
  DEBUG(dbgs() << "Boolean Logical instruction: " << I << "\n");
  if (isTrackedCondFlag(&I)){
    // Make sure we make a copy here
    TBool * LHS = new TBool(*TrackedCondFlags[&I]);    
    if (TBool *Op1 = getTBoolfromValue(I.getOperand(0))){
      if (TBool *Op2 = getTBoolfromValue(I.getOperand(1))){
	switch(I.getOpcode()){
	case Instruction::And:
	  LHS->And(Op1,Op2);
	  break;
	case Instruction::Or:
	  LHS->Or(Op1,Op2);
	  break;
	case Instruction::Xor:
	  LHS->Xor(Op1,Op2);
	  break;
	default:
	  llvm_unreachable("Wrong instruction in visitBooleanLogicalInst");
	}
	// We do not delete LHS since it will be stored in a map manipulated
	// by updateCondFlag. Instead, updateCondFlag will free the old
	// value if it is replaced with LHS.
	updateCondFlag(I,LHS);
	DEBUG(dbgs() << "\t[RESULT]");
	DEBUG(LHS->print(dbgs()));
	DEBUG(dbgs() << "\n");        
	return;
      }
    }
    // FIXME:
    // Here we don't consider an error yet because we have things like:
    // %tmp547.i = fcmp ugt float %tmp13.i83.i, 0.000000e+00
    // %tmp551.i = fcmp ult float %tmp13.i83.i, 1.000000e+00
    // %or.cond = and i1 %tmp547.i, %tmp551.i
    // where the lhs is a Boolean flag but the operands not.
    LHS->makeMaybe();
    return;
  }
  /*
  if (isCondFlag(I.getOperand(0)))
    dbgs() << I.getOperand(0)->getName() << " is a boolean flag\n";
  else
    dbgs() << I.getOperand(0)->getName() << " is NOT a boolean flag\n";
  if (isCondFlag(I.getOperand(1)))
    dbgs() << I.getOperand(1)->getName() << " is a boolean flag\n";
  else
    dbgs() << I.getOperand(1)->getName() << " is NOT a boolean flag\n";
  if (isTrackedCondFlag(I.getOperand(0)))
    dbgs() << I.getOperand(0)->getName() << " is  tracked \n";
  else
    dbgs() << I.getOperand(0)->getName() << " is NOT tracked\n";
  if (isTrackedCondFlag(I.getOperand(1)))
    dbgs() << I.getOperand(1)->getName() << " is tracked\n";
  else
    dbgs() << I.getOperand(1)->getName() << " is NOT tracked\n";
  */
  llvm_unreachable("All operands must be Boolean flags that are being tracked");
}


// Return true iff widening can be applied 
bool FixpointSSI::Widen(Instruction* I, unsigned NumChanges){
  return ( (WideningLimit > 0) && 
	    WideningPoints.count(I) &&
	   (NumChanges >= WideningLimit));
}    

///  This procedure is vital for the termination of the analysis since
///  it decides which points must be widen so that the analysis can
///  terminate. If we miss a point then we are in trouble.  We
///  consider mainly for widening points phi nodes that are in
///  destination blocks of backedges (arc whose tail dominates its
///  head).
///
///  Moreover, we also consider some load instructions done in the
///  destination block of backedges. In particular, where global
///  variables of interest are involved.
void FixpointSSI::addTrackedWideningPoints(Function * F){
  if (WideningLimit > 0){    
    SmallVector<std::pair<const BasicBlock*,const BasicBlock*>, 32> BackEdges;
    FindFunctionBackedges(*F, BackEdges);    
    // DestBackEdgeBB - Set of destination blocks of backedges
    SmallPtrSet<const BasicBlock*,16> DestBackEdgeBB;

    for (SmallVector<std::pair<const BasicBlock*,const BasicBlock*>,32>::iterator 
	   I = BackEdges.begin(),E = BackEdges.end(); I != E; ++I){
      // DEBUG(dbgs() << "backedge from" << I->first->getName() << " to " << 
      // 	  I->second->getName() << "\n");
      DestBackEdgeBB.insert(I->second);    
    }
    
    DEBUG(dbgs() << "Widening points: \n");
    for (inst_iterator I = inst_begin(F), E=inst_end(F) ; I != E; ++I){
      // A phi node that is in the destination block of a backedge
      if (PHINode *PN = dyn_cast<PHINode>(&*I)){
	if (PN->getNumIncomingValues() > 1){
	  if (DestBackEdgeBB.count(PN->getParent())){
	    DEBUG(dbgs() << "\t" << *I << "\n");
	    NumOfWideningPts++;
	    WideningPoints.insert(&*I);
	  }
	}
      }
      // A load of a global variable of interest done in the
      // destination block of a backedge
      if (LoadInst *LoadI = dyn_cast<LoadInst>(&*I)){
	if (GlobalVariable * Gv = 
	    dyn_cast<GlobalVariable>(LoadI->getPointerOperand())){
	  if (TrackedGlobals.count(Gv) && 
	      DestBackEdgeBB.count(I->getParent())){
	    DEBUG(dbgs() << "\t" << *I << "\n");
	    NumOfWideningPts++;
	    WideningPoints.insert(&*I);
	  }
	}
      }
    }
    DEBUG(dbgs() << "\n");
  }  
}


///////////////////////////////////////////////////////////////////////////
// Printing utililties
///////////////////////////////////////////////////////////////////////////

// Helper to make easier the printing of results and stats.
void sortByBasicBlock(Function *F, AbstractStateTy ValMap, 
		      DenseMap<BasicBlock*, std::set<AbstractValue*> * > & BlockMap){

  for (AbstractStateTy::iterator I=ValMap.begin(), E=ValMap.end(); I != E; ++I){    
    AbstractValue * AbsVal = I->second;
    if (!AbsVal) continue; // I think this should not happen!
    BasicBlock * BB = AbsVal->getBasicBlock();
    if (!BB) continue;
    DenseMap<BasicBlock*, std::set<AbstractValue*> * >::iterator II = BlockMap.find(BB);
    if (II != BlockMap.end()){
      std::set<AbstractValue*> *S = II->second;
       S->insert(AbsVal);
       BlockMap[BB] = S;
    }
    else{
      std::set<AbstractValue*> *S = new std::set<AbstractValue*>();
      S->insert(AbsVal);
      BlockMap.insert(std::make_pair(BB,S));
    }
  } // end for
} 

/// Print analysis results for global variables.
void FixpointSSI::printResultsGlobals(raw_ostream &Out){
  Out <<"\n===-------------------------------------------------------------------------===\n" ;
  Out << "                 Analysis Results for global variables \n" ;
  Out <<"===-------------------------------------------------------------------------===\n" ;      
  // Iterate over all global variables of interest defined in the module
  for (Module::global_iterator Gv = M->global_begin(), E = M->global_end(); Gv != E; ++Gv){
    if (TrackedGlobals.count(Gv)){
      ValueState[Gv]->print(Out);
      Out << "\n";
    }
  }
  Out << "\n";
}

/// Print results of the analysis for the particular function F.
void FixpointSSI::printResultsFunction(Function *F, raw_ostream &Out){
  Out <<"\n===-------------------------------------------------------------------------===\n" ;
  Out << "                 Analysis Results for " << F->getName() << "\n" ;
  Out << "                 (Only local variables are displayed) \n" ;
  Out <<"===-------------------------------------------------------------------------===\n" ;      

  DenseMap<BasicBlock*, std::set<AbstractValue*> * > BlockMap;
  sortByBasicBlock(F, ValueState, BlockMap);

  // Iterate over each basic block.
  for (Function::iterator BB = F->begin(), EE = F->end(); BB != EE; ++BB){
    DenseMap<BasicBlock*, std::set<AbstractValue*> * >::iterator 
      It = BlockMap.find(BB);
    if (BBExecutable.count(BB) == 0){
      Out << "Block " << BB->getName() << " is unreachable\n";
      continue;
    }
    
    if (It == BlockMap.end())
      Out << "Block " << BB->getName() << " {}\n";
    else{ 
      std::set<AbstractValue*> *Values = It->second;
      Out << "Block " << BB->getName() << " { ";       
      // Print abstract values of the block
      for(std::set<AbstractValue*>::iterator 
	    I_I = Values->begin(), I_E = Values->end(); I_I != I_E ; ++I_I){
        AbstractValue *AbsV =  (*I_I);
	AbsV->print(Out);
	Out << "; ";
      }
      Out << "}\n";
    }
  }
    
  // Boolean flags
  // for (DenseMap<Value*,TBool*>::iterator I=TrackedCondFlags.begin(), 
  // 	 E=TrackedCondFlags.end(); I!=E;++I){
  //   if (VST->lookup(I->first->getName()))
  //     Out << " " << I->first->getName() << "=" << I->second->getValue() << "; ";
  // }
}

/// Print the results of the analysis for the whole module.
void FixpointSSI::printResults(raw_ostream &Out){
  // Iterate over all functions defined in the module.
  for (Module::iterator F = M->begin(), E=M->end() ; F != E; ++F)
    printResultsFunction(F,Out);
}

void printValueInfo(Value *v, Function *F){      
  if (Argument *Arg = dyn_cast<Argument>(v))
    dbgs() << F->getName() << "." << Arg->getParent()->getName() 
	   << "." << Arg->getName() << " type(" << *Arg->getType() << ")\n";
	   
  else{
    if (GlobalVariable *Gv = dyn_cast<GlobalVariable>(v)){
      dbgs() << "global." << Gv->getName() 
	     << " type(" << *Gv->getType() << ")\n";
    }
    else{
      if (Instruction *Inst = dyn_cast<Instruction>(v)){
	if (Inst->hasName()){
	  dbgs() << F->getName() << "." << Inst->getParent()->getName() 
		 << "." <<  Inst->getName() 
		 << " type(" << *Inst->getType() << ")\n";
		   
	}
      }
    }
  }
}

void printUsersInst(Value *I,SmallPtrSet<BasicBlock*, 16> BBExecutable,
		    bool OnlyExecutable){ 
  dbgs() << "USERS of" << *I << ": \n";
  for (Value::use_iterator UI = I->use_begin(), E = I->use_end();
       UI != E; ++UI) {
    Instruction *U = cast<Instruction>(*UI);
    if (OnlyExecutable){
      if (BBExecutable.count(U->getParent()))       
	dbgs() << "\t" << *U << "\n";
    }
    else
      dbgs() << "\t" << *U << "\n";
  }
}
   



