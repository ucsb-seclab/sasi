// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.

//////////////////////////////////////////////////////////////////////////////
/// \file Fixpoint.cpp
///       Iterative Forward Abstract Interpreter 
//////////////////////////////////////////////////////////////////////////////

#include "Fixpoint.h"
#include "AbstractValue.h"

using namespace llvm;
using namespace unimelb;

STATISTIC(NumOfAnalFuncs     ,"Number of analyzed functions");
STATISTIC(NumOfAnalBlocks    ,"Number of analyzed blocks");
STATISTIC(NumOfAnalInsts     ,"Number of analyzed instructions");
STATISTIC(NumOfInfeasible    ,"Number of infeasible branches");
STATISTIC(NumOfWideningPts   ,"Number of widening locations");
STATISTIC(NumOfWidenings     ,"Number of applied widenings");
STATISTIC(NumOfNarrowings    ,"Number of narrowing iterations");
STATISTIC(NumOfSkippedIns    ,"Number of skipped instructions");
STATISTIC(NumOfUnreachable   ,"Number of unreachable blocks");

/// Debugging methods
void printValueInfo(Value *,Function*);
void printUsersInst(Value *,SmallPtrSet<BasicBlock*, 16>,bool, 
		    DenseMap<Value*, filter_users *>);
void printTrackedRecursiveFunctions(SmallPtrSet<Function*, 16>);
void printFilterUsers(DenseMap<Value*,filter_users*>);
inline void PRINTCALLER(std::string s){ /* dbgs() << s << "\n";*/ }

/// Return true if the instruction has a left-hand side.
inline bool HasLeftHandSide(Instruction &I){
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

/// Return true if Value is a Boolean flag: type of integer of i1.
inline bool  isCondFlag(Value *V){
  if (V->getType()->isIntegerTy(1))
    return true;   
  
  if (V->getType()->isPointerTy())
    return V->getType()->getContainedType(0)->isIntegerTy(1);
      
  return false;
}

/// Return true if the type of the instruction is of type 1-bit
/// integer and its opcode is either And, Or, or Xor.
bool IsBooleanLogicalOperator(Instruction *I){
  return (  I->getType()->isIntegerTy(1) && 
	    (I->getOpcode() == Instruction::And ||
	     I->getOpcode() == Instruction::Or ||
	     I->getOpcode() == Instruction::Xor ) ) ;
}


Fixpoint::
Fixpoint(Module *M, unsigned WL, unsigned NL, AliasAnalysis *AA):
  M(M),
  AA(AA),
  WideningLimit(WL),
  NarrowingLimit(NL),
  NarrowingPass(false),
  IsAllSigned(true){

  env = new Environment(M);
  // TG = new TimerGroup("Range Analysis Timing Measurements");
  // T0 = new Timer("Execute block"                          ,*TG);
  // T1 = new Timer("Notify users"                           ,*TG);
  // T2= new Timer("Generate filters"                       ,*TG);
  // T3= new Timer("Propagate from predecessors"            ,*TG);
  // T4= new Timer("Notify filter users"                    ,*TG);
  // T5= new Timer("Narrowing"             ,*TG);
  // T6= new Timer("Update State"             ,*TG);
  // T7= new Timer("Mark Executable Block "             ,*TG);
}

Fixpoint::
Fixpoint(Module *M, unsigned WL, unsigned NL, AliasAnalysis *AA, 
	 bool isSigned):
  M(M),
  AA(AA),
  WideningLimit(WL),
  NarrowingLimit(NL),
  NarrowingPass(false),
  IsAllSigned(isSigned){

  env = new Environment(M);
  // TG = new TimerGroup("Range Analysis Timing Measurements");
  // T0= new Timer("Execute block"                          ,*TG);
  // T1= new Timer("Notify users"                           ,*TG);
  // T2= new Timer("Generate filters"                       ,*TG);
  // T3= new Timer("Propagate from predecessors"            ,*TG);
  // T4= new Timer("Notify filter users"                    ,*TG);
  // T5= new Timer("Narrowing"             ,*TG);
  // T6= new Timer("Update State"             ,*TG);
  // T7= new Timer("Mark Executable Block "             ,*TG);

}

Fixpoint::~Fixpoint(){

  for(DenseMap<BasicBlock*, AbstractBlock*>::iterator 
	I = BasicBlockToAbstractBlock.begin(),
	E = BasicBlockToAbstractBlock.end(); I!=E; ++I){
    delete I->second;
  }

  for(DenseMap<Value*, TBool*>::iterator I = TrackedCondFlags.begin(),
	E = TrackedCondFlags.end(); I!=E; ++I){
    delete I->second;
  }

  for(DenseMap<Value*, filter_users *>::iterator 
	I = TrackedFilterUsers.begin(),
	E = TrackedFilterUsers.end(); I!=E; ++I){
    delete I->second;
  }

  for(DenseMap<Value*, AbstractValue*>::iterator 
	I = ConstValMap.begin(),
	E = ConstValMap.end(); I!=E; ++I){
    delete I->second;
  }

  for(DenseMap<Value*, AbstractValue*>::iterator 
	I = GlobalValMap.begin(),
	E = GlobalValMap.end(); I!=E; ++I){
    delete I->second;
  }

  delete env;
  // delete T1; delete T2;delete T3;delete T4;delete T5; delete T6; delete T7;
  // delete TG; 
}

inline void ResetAbstractValue(AbstractValue * V){
  V->makeBot();
}

void Fixpoint::init(Function *F, DominatorTree *DT){

  // Pessimistic assumption about trackable global variables
  // This makes the analysis almost useless with large programs. 
  addTrackedGlobalVariablesPessimistically(M);
  //addTrackedGlobalVariables(M);

  if (Utilities::IsTrackableFunction(F)){
    // Iterate over all formal parameters
    for (Function::arg_iterator argIt = 
	   F->arg_begin(), E=F->arg_end(); argIt != E; argIt++) {
      DEBUG(printValueInfo(argIt,F));
      if (isCondFlag(argIt)){
	DEBUG(dbgs() << "\trecording a Boolean flag:" << argIt->getName() << "\n");
	TrackedCondFlags.insert(std::make_pair(&*argIt, new TBool()));
      }
      else
	env->addVar(&*argIt); // env->addVar(&(F->getEntryBlock()) ,&*argIt);
    }
    
    // Iterate over each basic block.
    for (Function::iterator BB = F->begin(), EE = F->end(); BB != EE; ++BB){
      // Iterate over each instruction.
      for (BasicBlock::iterator I = BB->begin(), IE = BB->end(); I != IE; ++I){
	DEBUG(printValueInfo(&*I,F));
	if (HasLeftHandSide(*I)){
	  if (Value * V = dyn_cast<Value>(&*I)){
	    if (isCondFlag(V)){
	      DEBUG(dbgs() << "\trecording a Boolean flag:" << V->getName() << "\n");
	      TrackedCondFlags.insert(std::make_pair(&*V, new TBool()));
	    }	
	    else
	      env->addVar(&*V); //env->addVar(BB,&*V);
	  }
	}
      }
    }
    // Dominator tree for the function
    DTs.insert(std::make_pair(F,DT));
    // Create an abstract value for each integer constant in the program
    std::vector<std::pair<Value*,ConstantInt*> > NewAbsVals;
    Utilities::addTrackedIntegerConstants(F, IsAllSigned, 
					  ConstSet, NewAbsVals); 
    for (unsigned int i=0; i<NewAbsVals.size(); i++){
      ConstValMap.insert(std::make_pair(NewAbsVals[i].first,
					initAbsIntConstant(NewAbsVals[i].second)));   
    }
    // Record widening points
    addTrackedWideningPoints(F);      
  }
}


// Iterative global intraprocedural analysis.
void Fixpoint::solve(Function *F){
  solveLocal(F);
  //  T5->startTimer(); 
  computeNarrowing(F);
  // T5->stopTimer(); 
}


///  Cleanup some datastructures that still keep information from the
///  last analysis of the same function.
void Fixpoint::cleanupPreviousFunctionAnalysis(Function *F){
  DEBUG(dbgs() << "Cleanup previous analysis of the function: " 
	<< F->getName() << "\n");

  // To see the content of BBExecutable
  // DEBUG(dbgs() << "BBExecutable={");
  // for(SmallPtrSet<BasicBlock*, 16>::iterator I = BBExecutable.begin(),
  // 	E = BBExecutable.end(); I!=E; ++I){
  //   BasicBlock * BB = *I;
  //   if (BB->getParent() == F){
  //     DEBUG(dbgs() << BB->getParent()->getName() << "." << BB->getName() << ";");
  //   }
  // }
  // DEBUG(dbgs() << "}\n");

  // Delete all blocks in BBExecutable that belong to F

  // Expensive copy -- but we need it because SmallPtrSet does not
  // allow deleting elements while iterating through it
  SmallPtrSet<BasicBlock*, 16> BBExecutableCopy(BBExecutable);
  for(SmallPtrSet<BasicBlock*, 16>::iterator I = BBExecutableCopy.begin(),
	E = BBExecutableCopy.end(); I!=E; ++I){
    BasicBlock * BB = *I;
    if (BB->getParent() == F){
      DEBUG(dbgs() << "Erase from BBExecutable: " 
	           << BB->getParent()->getName() << "." << BB->getName() << "\n");
      BBExecutable.erase(BB);
    }
  }

  // Delete all edges in KnownFeasibleEdges that belong to F
  for(std::set<Edge>::iterator IF = KnownFeasibleEdges.begin(), 
	EF=KnownFeasibleEdges.end() ; IF != EF ; ++IF){
    Edge e = *IF;
    if (e.first->getParent() == F){
      DEBUG(dbgs() << "Erase from KnownFeasibleEdges: " 
	           <<  e.first->getParent()->getName() << "." 
	           << e.first->getName() << " --> "  
	           <<  e.second->getParent()->getName() << "." 
	           << e.second->getName() << "\n");
      KnownFeasibleEdges.erase(e);
    }
  }
}

// Compute a intraprocedural fixpoint until no change applying the
// corresponding transfer function.
void Fixpoint::solveLocal(Function *F){
  DEBUG(dbgs () << "Starting fixpoint for " << F->getName() << " ... \n");
  NumOfAnalFuncs++;
  // We need to cleanup BBExecutable and KnownFeasibleEdges in case
  // the function is analyzed more than once. Otherwise, after the
  // first time all blocks are kept as processed so nothing will be
  // done.
  cleanupPreviousFunctionAnalysis(F);
  markBlockExecutable(&F->getEntryBlock());    
  computeFixpo();
  DEBUG(dbgs () << "Fixpoint reached for " << F->getName() << ".\n");
}

/// It keeps track of two worklists: for blocks, BB-worklist, and for
/// instructions, I-worklist. The procedure runs until both are empty.
void Fixpoint::computeFixpo(){

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
      DEBUG(printUsersInst(I,BBExecutable,true,TrackedFilterUsers));
      // T1->startTimer();
      for (Value::use_iterator UI = 
	     I->use_begin(), E = I->use_end(); UI != E; ++UI) {
        Instruction *U = cast<Instruction>(*UI);
	// We check that the instruction U is defined in an executable
	// block
        if (BBExecutable.count(U->getParent()) && U != I) {
	  DEBUG(dbgs() << "\n***Visiting: " << *U << " as user of " 
		       << *I << "\n");      
          visitInst(*U);
	}
      } // end for
      // T1->stopTimer();
      /// If "I" is a variable used to filter other variables we need
      /// to notify to them.
      // T4->startTimer();
      if (filter_users *Users = TrackedFilterUsers[I]){
	Instruction * Inst = dyn_cast<Instruction>(I);
	assert(Inst && "This should not happen");
	AbstractBlock * AbsBlock = BasicBlockToAbstractBlock[Inst->getParent()]; 
	assert(AbsBlock && "This should not happen");
      	for(filter_users::iterator 
	      UI = Users->begin(),UE = Users->end() ; UI != UE; ++UI){
	  // Believe it or not we can have instructions where types do
	  // not match (e.g, t5-a.c):
	  //
	  //    %tmp = sext i8 %.0 to i32: 
	  //    %tmp2 = icmp slt i32 %tmp, %N
	  // 
	  // If we use cast then an exception is raised. If we use
	  // dyn_cast then no user will be found due to the type
	  // mismatch. Therefore, we will lose precision.
      	  if (Instruction * U = dyn_cast<Instruction>(*UI)){
	    if (BBExecutable.count(U->getParent())) {
	      DEBUG(dbgs() << "\n***Visiting: " << *U << " as user of filter " 
		           << *I << "\n");
	      notifyUser(I, Inst->getParent(), AbsBlock, U);
	      visitInst(*U);
	      // Moreover, we need to visit the users of the users of
	      // the filter.
	      for(Value::use_iterator 
		    UI2 = U->use_begin(), E2 = U->use_end(); 
		  UI2 != E2; ++UI2) {
		Instruction * U2 = cast<Instruction>(*UI2);
		if (BBExecutable.count(U2->getParent())) {
		  DEBUG(dbgs() << "\n***Visiting: " << *U2 
			       << " as user of filter " << *U << "\n");
		  notifyUser(U, Inst->getParent(), AbsBlock, U2);
		  visitInst(*U2);
		}
	      }
	    }
	  }
      	} // end for
      } 
      // T4->stopTimer();
    } // end while

    // Process the basic block work list.
    while (!BBWorkList.empty()) {
      std::set<BasicBlock*>::iterator BBIt = BBWorkList.begin();
      BBWorkList.erase(BBIt);
      BasicBlock *BB = *BBIt;

      // Generate filters for the block. This is done also only the
      // first time the block is reachable since they will not change
      // later on. To generate filters we rely on dominance
      // information.
      // T2->startTimer();
      DominatorTree *DT = DTs[BB->getParent()];
      assert(DT && "No dominance information for the block");
      if (DomTreeNode   *D_Curr = DT->getNode(BB)){
	while (DomTreeNode *D_ImmDom = D_Curr->getIDom()){
	  BasicBlock *ImmBB = D_ImmDom->getBlock();
	  generateFilters(BB, ImmBB );
	  D_Curr = D_ImmDom;
	}
      }
      // T2->stopTimer();
      // T3->startTimer();
      // Propagate values from predecessors to current block. Only
      // needed the first the block is reachable.
      propagatePredecessors(BB);
      // T3->stopTimer();
      DEBUG(dbgs() << "\n***Popped off BBWL: " << *BB);
      // T0->startTimer();
      // Execute the instructions of the block.
      for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I)
        visitInst(*I);
      // T0->stopTimer();
    } // end while
  } // end outer while
}


/// Iterate over all instructions in the function and apply the
/// transfer function for every one without widening. The instructions
/// must be visited following the original order in the program.
void Fixpoint::computeOneNarrowingIter(Function *F){
  markBlockExecutable(&F->getEntryBlock());    
  // Iterator dfs over the basic blocks in the function
  for (df_iterator<BasicBlock*>  DFI = df_begin(&F->getEntryBlock()), 
	 DFE = df_end(&F->getEntryBlock()); DFI != DFE; ++DFI) {   
    BasicBlock * BB = *DFI;
    if (BBExecutable.count(BB)){
      for (BasicBlock::iterator 
	     I = BB->begin(), E = BB->end(); I != E; ++I){
	visitInst(*I);
      }
    }
  }
}

/// Narrowing is implemented by making a arbitrary number of passes
/// applying the transfer functions **without** applying widening.
void Fixpoint::computeNarrowing(Function *EntryF){
  unsigned N = NarrowingLimit;
  NarrowingPass=true;
  while (N-- > 0){
    DEBUG(dbgs () << "\nStarting narrowing  ... \n");
    NumOfNarrowings++;    
    assert(InstWorkList.empty() && "The I-worklist should be empty");
    computeOneNarrowingIter(EntryF);
    assert(InstWorkList.empty() && "The I-worklist should be empty");
  } 
  NarrowingPass=false;
  DEBUG(dbgs () << "Narrowing finished.\n");
}

/// Mark a basic block B as executable, adding it to the BB-worklist
/// if it is not already executable.
void Fixpoint::markBlockExecutable(BasicBlock *B) {
  DEBUG(dbgs() << "***Marking Block Executable: " << B->getName() << "\n");
  NumOfAnalBlocks++;  
  BBExecutable.insert(B);   // Basic block is executable  
  BBWorkList.insert(B);     // Add the block to the work list
  //T7->startTimer();
  DenseMap<BasicBlock*,AbstractBlock*>::iterator I = 
    BasicBlockToAbstractBlock.find(B);  
  if (I == BasicBlockToAbstractBlock.end()){
    // We initialize all values with top!        
    //  SmallPtrSet<Value *, 32> Variables = env->getEnv(B);
    std::set<Value*> Variables = env->getEnv();
    MapValToAbstractTy valMap;
    // typedef SmallPtrSet<Value *, 32>::iterator It;    
    typedef std::set<Value*>::iterator It;
    for(It I= Variables.begin(), E=Variables.end(); I!=E; ++I){
      Value *V = *I;
      AbstractValue *AbsVal=NULL;
      if (isa<Instruction>(V))
	AbsVal = initAbsValBot(V);
      else
	AbsVal = initAbsValTop(V);
      assert(AbsVal);
      valMap.insert(std::make_pair(&*V,AbsVal));      
    } 
    AbstractBlock * AbsB = new AbstractBlock(B, valMap);
    BasicBlockToAbstractBlock.insert(std::make_pair(&*B,AbsB));
  }
  // T7->stopTimer();
}

/// Mark the edge Source-Dest as executable and mark Dest as an
/// executable block.  Moreover, we revisit the phi nodes of Dest.
void Fixpoint::markEdgeExecutable(BasicBlock *Source, BasicBlock *Dest) {
  if (!KnownFeasibleEdges.insert(Edge(Source, Dest)).second)
    return;  // This edge is already known to be executable!  
  DEBUG(dbgs() << "***Marking Edge Executable: " << Source->getName()
	       << " -> " << Dest->getName() << "\n");
  if (BBExecutable.count(Dest) && !NarrowingPass) {
    // The destination is already executable, but we just made an edge
    // feasible that wasn't before.  Revisit the PHI nodes in the block
    // because they have potentially new operands.
    for (BasicBlock::iterator I = Dest->begin(); isa<PHINode>(I); ++I)
      visitPHINode(*cast<PHINode>(I));    
  } 
  else 
    markBlockExecutable(Dest);
}

///  Return true if a transition between two blocks is feasible. An
///  edge is rarely always infeasible but it can be in a particular
///  fixpoint iteration (e.g., the first one) which is usually
///  important for precision of the analysis.
bool Fixpoint::isEdgeFeasible(BasicBlock *From, BasicBlock *To){
  std::set<Edge>::iterator I =  
    KnownFeasibleEdges.find(std::make_pair(From,To));  
  if (I != KnownFeasibleEdges.end()) 
    return true;
  else{
    NumOfInfeasible++;		  
    return false;
  }
}

/// Check if the new value is contained by the old value. If yes, then
/// return and do nothing.  Otherwise, add the instruction in the
/// I-worklist and apply widening if widening conditions are
/// applicable. If we are doing a narrowing pass then widening is
/// disabled and we do not add anything in the I-worklist.
void Fixpoint::updateState(Instruction &Inst   , MapValToAbstractTy &ValMap, 
			   AbstractValue * OldV, AbstractValue * NewV) {

  assert(NewV && "updateState: instruction not defined"); 
  
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
    /////////////////////////////////////////////////////////////////
    // For lubbing all possible values in case of interprocedural ///
    // NewV->join(OldV);
    /////////////////////////////////////////////////////////////////
    ValMap[&Inst] = NewV;
  }
  else{
    /////////////////////////////////////////////////////////////////
    // Widening:
    //             bottom         if n=0
    // f^{n}_{w} = f^{n-1}_{w}    if n>0 and 
    //                            f(f^{n-1}_{w}) \subseteq f^{n-1}_{w}
    //             widening(f^{n-1}_{w},f(f^{n-1}_{w})) otherwise
    // Here OldV = f^{n-1}_{w} and NewV = f(f^{n-1}_{w})
    /////////////////////////////////////////////////////////////////
    
    if (/*NewV->lessOrEqual(OldV)*/ NewV->isEqual(OldV)){
      DEBUG(dbgs() << "\nThere is no change\n");
      return;  
    }
    
    NewV->incNumOfChanges();        
    if (Widen(&Inst,NewV->getNumOfChanges())){
      NumOfWidenings++;
      NewV->widening(OldV,ConstSet);
      // We reset the counter because we do not want to apply widening
      // unless it is strictly needed. E.g., after a widening we can
      // have a casting operation. If the counter is not reset then we
      // will do widening again with potential catastrophic losses.
      NewV->resetNumOfChanges();
    }

    /////////////////////////////////////////////////////////////////
    // For lubbing all possible values in case of interprocedural ///
    // NewV->join(OldV);
    /////////////////////////////////////////////////////////////////
    ValMap[&Inst] = NewV;
    DEBUG(dbgs() << "***Added into I-WL: " << Inst << "\n");
    InstWorkList.insert(&Inst);
  }
  // T6->startTimer();
  // Notify to users to make consistent maps across different blocks.
  AbstractBlock * AbsBlock = BasicBlockToAbstractBlock[Inst.getParent()] ; 
  AbsBlock->updateValMap(ValMap);
  Value * I = cast<Value>(&Inst);
  for (Value::use_iterator 
	 UI = I->use_begin(), E = I->use_end(); UI != E; ++UI) {
    Instruction *U = cast<Instruction>(*UI);
    if (BBExecutable.count(U->getParent()) && U != I && 
	                   (U->getParent() != Inst.getParent())) 
      notifyUser(I, Inst.getParent(), AbsBlock, U);
  }
  // T6->stopTimer();
}

/// U is an user of V that lives in B but U may lives in another
/// block.  Propagate the changes occurred in V to U.
void Fixpoint::
notifyUser(Value *V, BasicBlock* B, AbstractBlock *AbsB, Instruction* U){

  if (AbstractBlock * UserAbsBlock  = BasicBlockToAbstractBlock[U->getParent()]){	
    keepConsistentMaps(B, AbsB, U->getParent(), UserAbsBlock, V);
    /// Special case: if the user is a phi node we need to
    /// propagate also the change to the incoming block of the phi
    /// node. Note that the incoming block is not necessarily B.
    if (PHINode *PN = dyn_cast<PHINode>(U)){
      for (unsigned i=0, N=PN->getNumIncomingValues(); i != N;i++) {
	if (BBExecutable.count(PN->getIncomingBlock(i)) &&  
	    (PN->getIncomingBlock(i) != V) && (PN->getIncomingBlock(i) != B)){
	  UserAbsBlock  = BasicBlockToAbstractBlock[PN->getIncomingBlock(i)];
	  assert(UserAbsBlock && "This should not happen");
	  keepConsistentMaps(B, AbsB, PN->getIncomingBlock(i), UserAbsBlock, V);
	}
      }
    }
  }
}

/// Propgate the abstract value associated with V from FromB to ToB.
/// Moreover, it runs any filter that may exist in ToB.
void Fixpoint::keepConsistentMaps(BasicBlock * FromB, AbstractBlock *FromAbsB, 
				  BasicBlock * ToB  , AbstractBlock *ToAbsB,
				  Value *V){
  if (FromB == ToB) return;

  DEBUG(dbgs() << "Propagating " << FromB->getName() << "#" 
	<< V->getName() << " to " << ToB->getName() << "#" 
	<< V->getName() << "\n");
	
  
  // 1st key step: keep consistent maps across blocks.
  // AbstractBlock * ToAbsB  = BasicBlockToAbstractBlock[ToB];
  MapValToAbstractTy ToValMap = ToAbsB->getValMap();
  delete ToValMap[V];
  // deep copy
  AbstractValue * AbsV  = FromAbsB->getValMap()[V]->clone();
  ToValMap[V] = AbsV;
  // 2nd key step: refine some values using information from
  // conditionals.
  evalFilter(AbsV, ToAbsB->getFilters(), ToValMap);
  ToAbsB->updateValMap(ToValMap);
}


/// The lhs of I is a Boolean flag. If change then I is added into the
/// I-worklist.
void Fixpoint::updateCondFlag(Instruction &I, TBool * New){  
  assert(isTrackedCondFlag(&I));  
  if (NarrowingPass){
    TrackedCondFlags[&I] = New;    
    return;
  }  
  TBool * Old = TrackedCondFlags.lookup(&I);  
  if (Old->isEqual(New)){
    DEBUG(dbgs() << "\nThere is no change\n");
    return;  
  }  
  TrackedCondFlags[&I] = New;
  DEBUG(dbgs() << "***Added into I-WL: " << I << "\n");
  InstWorkList.insert(&I);
}


/// Propagate abstract values from predecessors to current block. This
/// is only done the first time the block is reachable. After that,
/// whenever an instruction changes some abstract value at a block B
/// we update directly the other user's abstract values in B and also
/// in other blocks if the users are in other blocks.
void Fixpoint::propagatePredecessors(BasicBlock *Curr){
  // Special case: no predecessor
  if (pred_begin(Curr) == pred_end(Curr)) return;
  
  for (pred_iterator P = pred_begin(Curr); P != pred_end(Curr); ++P){
    if (isEdgeFeasible(*P,Curr)){
      AbstractBlock  * PredAbsB = BasicBlockToAbstractBlock[*P];
      AbstractBlock  * CurrB    = BasicBlockToAbstractBlock[Curr];
      assert(PredAbsB);
      assert(CurrB);

      MapValToAbstractTy PredMap = PredAbsB->getValMap();
      MapValToAbstractTy CurrMap = CurrB->getValMap();      
      DEBUG(dbgs() << "Propagating the whole map from " 
	    << (*P)->getName() << " to " << Curr->getName() << "\n");	       
      
      SmallPtrSet<AbstractValue*,32> CandidatesToFilter;
      for (MapValToAbstractTy::iterator 
	     I = CurrMap.begin(), E= CurrMap.end(); I!=E; ++I){
	AbstractValue *PredAbsV = PredMap[(*I).first]; 
	if (!PredAbsV){
	  // FIXME: not sure if this is normal behavior but it can
	  // happen.
	  assert(!(GlobalValMap[(*I).first]) && "Should look for in GlobalValMap");
	  continue;
	}
	AbstractValue *CurrAbsV = (*I).second; 
	assert(CurrAbsV);
	// - If PredAbsV is bottom nothing changes so no need of
	//   propagation.
	// - If PredAbsV is not alive (in the sense of live variable
	//   analysis) in Curr we should not propagate it neither.
	//   Note that in fact if PredAbsV is not alive should not
	//   occupy space in the abstract block associated with
	//   Curr. For now, it does. If high memory consumption is
	//   observed this may be one of the causes.
	if (!PredAbsV->isBot()) {	  
	  DEBUG(dbgs() << "\tpropagating " << PredAbsV->getValue()->getName() 
		       << "  from " << (*P)->getName() << " to "
		       << Curr->getName() << "\n");	       
	  CurrAbsV->join(PredAbsV);
	  CandidatesToFilter.insert(CurrAbsV);
	}	
      } // end inner for
      typedef SmallPtrSet<AbstractValue*,32>::iterator It;
      for(It I=CandidatesToFilter.begin(), E=CandidatesToFilter.end(); I!=E; ++I){
       	AbstractValue *AbsV = *I;
       	evalFilter(AbsV, CurrB->getFilters(), CurrMap);
      } // end inner for
      CurrB->updateValMap(CurrMap);
    }
  } // end outer for
}

/// We find out if a predecessor of the current block has a BranchInst
/// as a terminator. If the branch is conditional then we can refine
/// the abstract state using information from the conditional branch.
///
/// It is important to notice that it would be incorrect if a block
/// has more than one predecessor to execute the filters of each
/// predecessor and then join the results.
void Fixpoint::generateFilters(BasicBlock * B, BasicBlock *Predec){

  // Shortcut for entry block 
  if (pred_begin(B) == pred_end(B)) return;

  unsigned width;
  TerminatorInst * TI  = (Predec)->getTerminator();
  if (BranchInst * BI  = dyn_cast<BranchInst>(TI)){
    if (BI->isConditional()){
      AbstractBlock * AbsB = BasicBlockToAbstractBlock[B];	
      if (ICmpInst * CI = dyn_cast<ICmpInst>(BI->getCondition())){
	// If it is not of the type and width that we can track then
	// no bother
	if (Utilities::getIntegerWidth(CI->getType(),width))
	  AbsB->visitInstrToFilter(BI,CI, DTs[B->getParent()], 
				   DTCache, TrackedFilterUsers);
      }
      else if (SelectInst * SI = dyn_cast<SelectInst>(BI->getCondition())){
	// If it is not of the type and width that we can track then
	// no bother
	if (Utilities::getIntegerWidth(SI->getType(),width))
	  AbsB->visitInstrToFilter(BI, SI, DTs[B->getParent()], 
				   DTCache, TrackedFilterUsers);
      }
      else if (IsBooleanLogicalOperator(dyn_cast<Instruction>(BI->getCondition()))){
	AbsB->visitInstrToFilter(BI, cast<Instruction>(BI->getCondition()), 
				 TrackedCondFlags, DTs[B->getParent()], 
				 DTCache, TrackedFilterUsers); 
      }
      else if (PHINode *PHI = dyn_cast<PHINode>(BI->getCondition())){
#ifdef  WARNINGS
	dbgs() << "Warning: no filter generated for " << *PHI << "\n";
#endif  /*WARNINGS*/
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
#ifdef  WARNINGS
	dbgs() << "Warning: no filter generated for " << *FCI << "\n";
#endif  /*WARNINGS*/
      }
      else if (LoadInst *LI = dyn_cast<LoadInst>(BI->getCondition())){
#ifdef  WARNINGS
	dbgs() << "Warning: no filter generated for " << *LI << "\n";
#endif  /*WARNINGS*/
	}
      else{
	dbgs() << "Uncovered case by visitInstrToFilter: \n\t";
	dbgs() <<  *(BI->getCondition()) << "\n";
	dbgs() << "We may avoid the analysis losing precision!\n";
	// Temporary raise exception to be aware of the unsupported case.
	assert(false);		
      }
    }
  }
}

/// For reducing the number of cases, normalize the constraint with
/// respect to V. V appears always as the first argument in F.
void normalizeConstraint(BinaryConstraint *&F, Value *V){
  bool isOp1Constant = isa<ConstantInt>(F->getOperand(0));
  bool isOp2Constant = isa<ConstantInt>(F->getOperand(1));
  assert(!(isOp1Constant && isOp2Constant));
  if (isOp1Constant && !isOp2Constant){
    // We swap operands to have first operand the variable and the
    // second the constant
    F->swap();
  }    
  else if (!isOp1Constant && !isOp2Constant){
    assert( (F->getOperand(0) == V) || (F->getOperand(1) == V));
    if (F->getOperand(1) == V){
      // We swap operands to have first operand the variable that we
      // want to refine.
      F->swap();
    }
  }    
}

/// Execute the filters generated for AbsV. Each variable used in the
/// filter is mapped to its corresponding abstract value using valMap.
void Fixpoint::evalFilter(AbstractValue * &AbsV, 
			  const FiltersTy          filters, 
			  const MapValToAbstractTy valMap){
  assert(AbsV);
  Value* V = AbsV->getValue();
  assert(V);
  FiltersTy::const_iterator I = filters.find(V);
  if (I != filters.end()){
    BinaryConstraintSetTy * Rhs = I->second;
    for (BinaryConstraintSetTy::iterator 
	   II=Rhs->begin(), EE=Rhs->end(); II!=EE; ++II){
      BinaryConstraint *C = *II;
      DEBUG(dbgs() << "\tEvaluating filter constraints: "; 
	    C->print();  dbgs() << "\n");
      normalizeConstraint(C,V);
      DEBUG(dbgs() << "\tAfter normalization          : "; 
	    C->print();  dbgs() << "\n");
      AbstractValue * Op1 = Lookup(valMap, C->getOperand(0), true);
      AbstractValue * Op2 = Lookup(valMap, C->getOperand(1), true);
      unsigned pred       = C->getPred();
      // dbgs()<< "-----------------------------------------\n";
      // AbsV->print(dbgs());
      // dbgs() << "  ";
      // Op1->print(dbgs());
      // dbgs() << "  ";
      // Op2->print(dbgs());
      // dbgs()<< "\n-----------------------------------------\n";
      AbsV->filterSigma(pred, Op1->clone(), Op2->clone());
      // dbgs()<< "-----------------------------------------\n";
      DEBUG(dbgs() <<"\t";
	    AbsV->print(dbgs());
	    dbgs() << "\n");
      // dbgs()<< "\n-----------------------------------------\n";
    }
  }
}

// Execute the instruction in the underlying abstract domain.
void Fixpoint::visitInst(Instruction &I) { 

  NumOfAnalInsts++;
  // First, special instructions handled directly by the fixpoint
  // algorithm, never passed into the underlying abstract domain
  // because they can be defined in terms of standard operations such
  // as join, meet, etc.
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

  AbstractBlock *AbsB = FindMap(&I);
  MapValToAbstractTy ValMap = AbsB->getValMap();

  // Otherwise, we pass the execution of the instruction to the
  // underlying abstract domain.
  if (Value *V = dyn_cast<Value>(&I)){
    if (AbstractValue * OldV = Lookup(ValMap, V, false)){ 
      AbstractValue *NewV = NULL;
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
	  // We can have instructions like 
	  // %tmp65 = sub i32 %tmp64, ptrtoint ([6 x %struct._IO_FILE*]* @xgets.F to i32)	    
	  // Therefore, we need to check if the operands are in
	  // ValMap. If not, just top.
	  AbstractValue * Op1 = Lookup(ValMap, I.getOperand(0), false);
	  AbstractValue * Op2 = Lookup(ValMap, I.getOperand(1), false);
	  if (Op1 && Op2)
	    NewV = OldV->visitArithBinaryOp(Op1,Op2,
					    I.getOpcode(),I.getOpcodeName());
	  else{
	    NewV=OldV->clone();
	    NewV->makeTop();	      
	  }
	}
	break;
      case Instruction::Shl:	// logical left shift
      case Instruction::LShr:	// logical right shift    
      case Instruction::AShr:	// arithmetic right shift    
      case Instruction::And:    // bitwise and
      case Instruction::Or:     // bitwise or
      case Instruction::Xor:    // bitwise xor
	DEBUG(dbgs() << "Bitwise instruction: " << I << "\n");
	NewV =  OldV->visitBitwiseBinaryOp(Lookup(ValMap, I.getOperand(0), true), 
					   Lookup(ValMap, I.getOperand(1), true),
					   I.getOperand(0)->getType(), 
					   I.getOperand(1)->getType(),
					   I.getOpcode() , I.getOpcodeName());
	break;
      case Instruction::BitCast: // no-op cast from one type to another
      case Instruction::ZExt:    // zero extend integers
      case Instruction::SExt:    // sign extend integers
      case Instruction::Trunc:   // truncate integers
	{
	  DEBUG(dbgs() << "Casting instruction: " << I << "\n");	    
	  // Special step: the source of the casting instruction may
	  // be a Boolean Flag.  If yes, we need to convert the
	  // Boolean flag into an abstract value. This must be done
	  // by the class that implements AbstractValue.
	  TBool         *SrcFlag = NULL;
	  AbstractValue *SrcAbsV = NULL;	  
	  if (isTrackedCondFlag(I.getOperand(0)))
	    SrcFlag = TrackedCondFlags.lookup(I.getOperand(0));
	  else
	    SrcAbsV = Lookup(ValMap, I.getOperand(0), true);
	  // At this point only either SrcAbsV or SrcFlag can be NULL
	  assert(SrcFlag || SrcAbsV);
	  NewV =  OldV->visitCast(I, SrcAbsV, SrcFlag, IsAllSigned);
	}
	break;
      default: 
#ifdef  WARNINGS
	dbgs() << "Warning: transfer function not implemented: " << I << "\n"; 
#endif  /*WARNINGS*/
	assert(NewV == NULL);
	NewV = OldV->clone();
	NewV->makeTop();
	NumOfSkippedIns++;
	break;
      } // end switch

      assert(NewV && "Something wrong during the transfer function ");
      PRINTCALLER("visitInst");
      updateState(I, ValMap, OldV, NewV);
      AbsB->updateValMap(ValMap);      
    }
  }
}

// Function calls


// Conservative assumptions if the code of the function is not
// available to the analysis or intraprocedural analysis.
void Fixpoint::
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
      AbstractBlock * AbsB      = BasicBlockToAbstractBlock[I->getParent()];
      MapValToAbstractTy ValMap = AbsB->getValMap();
      if (AbstractValue * LHS = Lookup(ValMap,dyn_cast<Value>(I),false)){
	DEBUG(dbgs() << "\tMaking the return value top: ");
	LHS->makeTop();
	DEBUG(LHS->print(dbgs()));
	DEBUG(dbgs() << "\n");
      }
    }
  }  

  // Make top all global variables that may be touched by the
  // function (CInst).
  if (Callee){
    for (SmallPtrSet<GlobalVariable*, 64>::iterator 
	   I = TrackedGlobals.begin(), E = TrackedGlobals.end();
	   I != E; ++I){    
      GlobalVariable *Gv = *I;
      AliasAnalysis::ModRefResult IsModRef = 
	AA->getModRefInfo(CInst,Gv,AliasAnalysis::UnknownSize);
      if ( (IsModRef ==  AliasAnalysis::Mod) || 
	   (IsModRef ==  AliasAnalysis::ModRef) ){ 	
	if (isTrackedCondFlag(Gv)){
	  TBool * GvFlag = TrackedCondFlags[Gv];    
	  assert(GvFlag && "ERROR: flag not found in TrackedCondFlags");
	  GvFlag->makeMaybe();
	  DEBUG(dbgs() <<"\tGlobal Boolean flag " << Gv->getName() 
		<< " may be modified by " 
		<< Callee->getName() <<".\n");
	}
	else{
	  AbstractValue * AbsGv = GlobalValMap.lookup(Gv);
	  assert(AbsGv && "ERROR: entry not found in GlobalValMap");
	  AbsGv->makeTop();
	  DEBUG(dbgs() <<"\tGlobal variable " << Gv->getName() 
		<< " may be modified by " 
		<< Callee->getName() <<".\n");
	}
      }
    }
  }
}

void Fixpoint::visitCallInst(CallInst &CI) { 

  CallSite *CS   = new CallSite(&CI); 
  Function *F    = CS->getCalledFunction();
  Instruction *I = CS->getInstruction();

  DEBUG(dbgs() << "Function call " << *I << "\n");	    

  // Since the analysis is intraprocedural we do not analysis the
  // callee.  We just consider the most pessimistic assumptions about
  // the callee: top for the return value and anything memory location
  // of interest (i.e., some global variables) may-touched by the
  // callee.
  FunctionWithoutCode(&CI,F,I);		       
  return;
}
void Fixpoint::visitReturnInst(ReturnInst &I){ 
  return;
}

/// Inform the analysis that it should track loads and stores to the
/// specified global variable if it can and it gives an initial
/// abstract value for each global variable. Note we follow C
/// semantics and assign 0 to all uninitialized integer scalar global
/// variables.
void Fixpoint::addTrackedGlobalVariables(Module *M) {
  /// Keep track only integer scalar global variables whose addresses
  /// have not been taken. In LLVM, if the address has not been taken
  /// then they memory object still has its def-use chains.
  for (Module::global_iterator 
	 Gv = M->global_begin(), E = M->global_end(); Gv != E; ++Gv){
    if (!Utilities::AddressIsTaken(Gv) &&
	Gv->getType()->isPointerTy() &&
	Gv->getType()->getContainedType(0)->isIntegerTy())
      {
	DEBUG(printValueInfo(Gv,NULL));
	// Initialize the global variable
	if (Gv->hasInitializer()){
	  if (ConstantInt * GvInitVal  = 
	      dyn_cast<ConstantInt>(Gv->getInitializer())){
	    if (isCondFlag(Gv)){
	      DEBUG(dbgs() << "\trecording a Boolean flag for global:" 
		    << Gv->getName() << "\n");
	      /// \fixme We ignore the initialized value and assume
	      /// "maybe".
	      TrackedCondFlags.insert(std::make_pair(&*Gv, new TBool()));
	    }
	    else	
	      GlobalValMap.insert(std::make_pair(&*Gv,initAbsValIntConstant(Gv,GvInitVal)));
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
	      GlobalValMap.insert(std::make_pair(&*Gv,initAbsValIntConstant(Gv,Zero)));
	    }
	}
	TrackedGlobals.insert(Gv);
      }    
  }
}


/// Keep track of global variables but we always initialize them with
/// top so that each function is analyzed with correct assumption.
void Fixpoint::addTrackedGlobalVariablesPessimistically(Module *M) {
  // Keep track only integer scalar global variables whose addresses
  // have not been taken. In LLVM, if the address has not been taken
  // then they memory object still has its def-use chains.
  for (Module::global_iterator Gv = M->global_begin(), E = M->global_end(); 
       Gv != E; ++Gv){
    if (!Utilities::AddressIsTaken(Gv) &&
	Gv->getType()->isPointerTy() &&
	Gv->getType()->getContainedType(0)->isIntegerTy())
      {
	DEBUG(printValueInfo(Gv,NULL));
	// Initialize the global variable
	if (isCondFlag(Gv)){
	  DEBUG(dbgs() << "\trecording a Boolean flag for global:" 
		<< Gv->getName() << "\n");
	  TrackedCondFlags.insert(std::make_pair(&*Gv,new TBool()));	      
	}
	else
	  GlobalValMap.insert(std::make_pair(&*Gv,initAbsValTop(Gv)));
	TrackedGlobals.insert(Gv);
      }    
  }
}

/// The store instruction is special since the destination is a
/// pointer which is not in SSA. We perform weak updates and also very
/// importantly, notify widening points about the change.
void Fixpoint::visitStoreInst(StoreInst &I){

  // We care only about store related to tracked global variables
  if (GlobalVariable *Gv = dyn_cast<GlobalVariable>(I.getPointerOperand())){
    if (TrackedGlobals.count(Gv)){
      // Special case if a Boolean Flag
      if (isTrackedCondFlag(Gv)){
	TBool * MemAddFlag = TrackedCondFlags[I.getPointerOperand()];    
	assert(MemAddFlag && "Memory location not mapped to a Boolean flag");
	DEBUG(dbgs() << "Write in a global variable " << I << "\n");	  
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
      AbstractBlock *AbsBB = BasicBlockToAbstractBlock[I.getParent()];
      assert(AbsBB);
      MapValToAbstractTy ValMap = AbsBB->getValMap();        
      AbstractValue * MemAddr = Lookup(ValMap, I.getPointerOperand(), true); 
      DEBUG(dbgs() << "Memory store " << I << "\n");	  
      //  printUsersInst(&I,BBExecutable, TrackedFilterUsers);      	
      // Weak update
      MemAddr->join(Lookup(ValMap, I.getValueOperand(), true));	
      DEBUG(dbgs() <<"\t[RESULT] ");
      DEBUG(MemAddr->print(dbgs()));
      DEBUG(dbgs() <<"\n");      
      
      // Notify widening points about new change. 
      // FIXME: In fact we could test here if there is actually a
      // change. Otherwise, we don't need to notify anybody.
      // FIXME: maybe also other load instructions which postdominate
      // I?
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

/// Load the abstract value from the memory pointer to the lhs of the
/// instruction and insert into the worklist all its users. We care
/// only about tracked global variables.
void Fixpoint::visitLoadInst(LoadInst &I){
  /// We care only about store related to tracked global variables
  if (GlobalVariable *Gv = dyn_cast<GlobalVariable>(I.getPointerOperand())){
    if (TrackedGlobals.count(Gv)){
      // Special case if a Boolean Flag:
      if (isTrackedCondFlag(Gv)){
	TBool * LHSFlag = TrackedCondFlags[&I];    
	assert(LHSFlag && "Memory location not mapped to a Boolean flag");
	if (isTrackedCondFlag(I.getPointerOperand())){
	  TBool * MemAddFlag = TrackedCondFlags[I.getPointerOperand()];
	  LHSFlag->makeTrue();
	  LHSFlag->And(LHSFlag,MemAddFlag);
	}
	else
	  LHSFlag->makeMaybe();
	updateCondFlag(I,LHSFlag);
	DEBUG(dbgs() << "\t[RESULT] ");
	DEBUG(LHSFlag->print(dbgs()));
	DEBUG(dbgs() << "\n");            
	return;
      }


      AbstractBlock *AbsB = FindMap(&I);      
      MapValToAbstractTy ValMap = AbsB->getValMap();
      AbstractValue * OldLHS    = Lookup(ValMap, &I, false);
      if (!OldLHS)
	return;      
      DEBUG(dbgs() << "Read from a global variable " << I << "\n");	  
      // Cloning in order to compare with old value in updateState
      AbstractValue * NewLHS = OldLHS->clone();        
      // Assign from memory to lhs
      ResetAbstractValue(NewLHS);
      NewLHS->join(Lookup(ValMap, I.getPointerOperand(), true));      
      DEBUG(dbgs() << "\t[RESULT] ");
      DEBUG(NewLHS->print(dbgs()));
      DEBUG(dbgs() << "\n");                  
      // Compare if it loads a new value and then add I into the
      // worklist
      PRINTCALLER("visitLoadInst");
      updateState(I, ValMap, OldLHS, NewLHS);
      AbsB->updateValMap(ValMap);      
      return;
    }
  }
  DEBUG(dbgs() << "Ignored memory load " << I << "\n");	  
}
		
/// Merges the abstract values of the incoming values only if the
/// incoming blocks are feasible. The implementation is fairly
/// straightforward due to two main restrictions:
///
/// \li Each PHI instruction is processed separately. This may lose
/// precision if the underlying abstract domain is relational.
///
/// \li An abstract state is simply a map from variables to abstract
/// values extended with bottom. Therefore, we do not need
/// renaming. We just take the abstract value from the predecessor,
/// refine it (if possible) and join it.
///
void Fixpoint::visitPHINode(PHINode &PN) {

  AbstractBlock *AbsCurrBB      = FindMap(&PN);      
  MapValToAbstractTy CurrValMap = AbsCurrBB->getValMap();

  if (Value *V = dyn_cast<Value>(&PN)){
    if (AbstractValue * OldV = Lookup(CurrValMap, V, false)){       
      AbstractValue *NewV = OldV->clone();
      ResetAbstractValue(NewV);
      DEBUG(dbgs() << "PHI node " << PN << "\n");
      for (unsigned i=0, num_vals=PN.getNumIncomingValues(); 
	   i != num_vals;i++) {
	if (PN.getIncomingValue(i)->getValueID() == Value::UndefValueVal) 
	  continue;
	if (isEdgeFeasible(PN.getIncomingBlock(i), PN.getParent())){				   
	  // Since join can only lose precision we stop if we already
	  // reach top.
	  if (NewV->IsTop()) 	      
	    break;
	  AbstractBlock *AbsPredecBB = 
	    BasicBlockToAbstractBlock[PN.getIncomingBlock(i)];
	  assert(AbsPredecBB);
	  MapValToAbstractTy PredecValMap = AbsPredecBB->getValMap();  

	  if (AbstractValue * AbsIncomingV = PredecValMap[PN.getIncomingValue(i)]){
	    // Important to make a copy here since we do not want to
	    // refine the abstract value in the predecessor abstract
	    // block.
	    AbstractValue * RefinedAbsIncomingV = AbsIncomingV->clone();
	    evalFilter(RefinedAbsIncomingV, AbsCurrBB->getFilters(), PredecValMap);
	    NewV->join(RefinedAbsIncomingV);
	    delete RefinedAbsIncomingV;
	  }
	  else{
	    // If the incoming value is a constant then we do not
	    // refine it.
	    NewV->join(Lookup(PredecValMap,PN.getIncomingValue(i), true));
	  }
	}
      } // end for
      PRINTCALLER("visitPHI");
      updateState(PN, CurrValMap, OldV, NewV);
      AbsCurrBB->updateValMap(CurrValMap);      
      DEBUG(dbgs() << "\t[RESULT] " << AbsCurrBB->getBasicBlock()->getName() << "#");
      DEBUG(NewV->print(dbgs()));
      DEBUG(dbgs() << "\n");        
    } 
  } 
}

/// Join the abstract values of the two operands and store it in the
/// lhs. If it is known whether the condition is true or false the
/// join can be refined. We have a separate treatment if the operands
/// are Boolean flags.
void Fixpoint::visitSelectInst(SelectInst &Ins){
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
    updateCondFlag(Ins,LHS);
    DEBUG(dbgs() << "\t[RESULT] ");
    DEBUG(LHS->print(dbgs()));
    DEBUG(dbgs() << "\n");        
    return;
  }

  // General case: all the operands are AbstractValue objects.

  AbstractBlock *AbsB = FindMap(&Ins);      
  MapValToAbstractTy ValMap = AbsB->getValMap();
  AbstractValue * OldLHS = Lookup(ValMap, &Ins, false);
  if (!OldLHS) return;
  // Cloning here to be able to compare old value later.
  AbstractValue * NewLHS= OldLHS->clone();  
  AbstractValue * True  = Lookup(ValMap, Ins.getTrueValue() , false);
  AbstractValue * False = Lookup(ValMap, Ins.getFalseValue(), false);
  // We can have instructions like:
  // %tmp128 = select i1 %tmp126, i32 -1, i32 %tmp127
  // where %tmp127 is not mapped.
  if (!True || !False){
    NewLHS->makeTop();
    goto END_GENERAL;
  }
    
  ResetAbstractValue(NewLHS);  
  if (!isTrackedCondFlag(Ins.getCondition())){
    // The condition is not trackable as a Boolean Flag so we join
    // both
    NewLHS->join(True);
    NewLHS->join(False);    
  }
  else{   
      TBool * Cond = TrackedCondFlags.lookup(Ins.getCondition());
      if (Cond->isTrue()){    // must be true
	NewLHS->join(True);
	// Not sure if this case is possible assuming constant
	// propagation is always done.
	// if (Instruction * SelCondIns = dyn_cast<Instruction>(Ins.getCondition()))
	//     AbsB->visitBoolInstrToFilter(true, SelCondIns, TrackedCondFlags, TrackedFilterUsers);
      }
      else{
	if (Cond->isFalse()){ // must be false
	  NewLHS->join(False);
	  // Not sure if this case is possible assuming constant
	  // propagation is always done.
	  // if (Instruction * SelCondIns = dyn_cast<Instruction>(Ins.getCondition()))
	  //     AbsB->visitBoolInstrToFilter(false, SelCondIns, TrackedCondFlags, TrackedFilterUsers);
	}
	else{                // maybe
	  NewLHS->join(True);
	  NewLHS->join(False);	  
	}
      }
  }
 END_GENERAL:
  PRINTCALLER("visitSelectInst");
  updateState(Ins, ValMap, OldLHS, NewLHS);
  AbsB->updateValMap(ValMap);      

  DEBUG(dbgs() << "\t[RESULT] ");
  DEBUG(NewLHS->print(dbgs()));
  DEBUG(dbgs() << "\n");          
}


/// Mark all possible executable transitions from the terminator.
void Fixpoint::visitTerminatorInst(TerminatorInst &TI){

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
    // FIXME: all the abstract values should be bottom here!
    DEBUG(dbgs() << "Unreachable instruction. \n") ;
    return;
  }

  dbgs() << TI << "\n";
  assert(false && "Found a terminator instruction that we do not support");
}

/// Reduce the number of cases. After calling getPredicate and swap,
/// only six cases: EQ, NEQ, SLE, ULE, ULT, and SLT.
/// 
/// Important: if an instruction is swap it may disable some def-use
/// chains. This causes to reach too early fixpoints (e.g.,
/// test-unbounded-loop-3.c). This weird behaviour is not documented
/// so it's hard to see why. Our solution is to clone the instruction
/// which we want to swap. However, we have to be careful since if we
/// try to lookup in one of our maps using that cloned instruction the
/// search will fail.
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

/// Compare if I1 and I2 are (not) equal and store the result (Boolean
/// value) into LHS. The flag meetIsBottom is true if the meet between
/// I1 and I2 is bottom (i.e., disjoint). We use it to reduce
/// uncertainty.
void comparisonEqInst(TBool &LHS,  AbstractValue *I1, AbstractValue *I2, 
		      bool meetIsBottom, unsigned OpCode){
  // Pre: this method cannot be called if V1 or V2 is bottom		      
  switch (OpCode){
  case ICmpInst::ICMP_EQ:
    if (!meetIsBottom){         // must be true or maybe
      if(I1->isEqual(I2))
	LHS.makeTrue();         // must be true
      else
	LHS.makeMaybe();
    }
    else                        // must be false
      LHS.makeFalse();  
    break;
  case ICmpInst::ICMP_NE:
    if (meetIsBottom)
      LHS.makeMaybe();          // must be true
    else{                       // must be false or maybe
      if(I1->isEqual(I2))
	LHS.makeFalse();  
      else
	LHS.makeMaybe();
    }
    break;
    assert( false && "ERROR: undefined argument in predEquality ");
  }
}

/// Compare if V1 is (signed) less or equal than V2 and store the
/// result in LHS as a Boolean value.
void comparisonSleInst(TBool &LHS, AbstractValue* V1, AbstractValue *V2){ 
  // Pre: this method cannot be called if V1 or V2 is bottom
  // if (V1->isBot() || V2->isBot()){
  //   LHS.makeMaybe();
  //   return;
  // }            
  if (V1->comparisonSle(V2)){
    if (V2->comparisonSlt(V1))
      LHS.makeMaybe();   
    else
      LHS.makeTrue();   // must be true
  }
  else
    LHS.makeFalse();    // must be false
}

/// Compare if V1 is (signed) less than V2 and store the result in LHS
/// as a Boolean value.
void  comparisonSltInst(TBool &LHS, AbstractValue *V1, AbstractValue*V2){
  // Pre: this method cannot be called if V1 or V2 is bottom
  // if (V1->isBot() || V2->isBot()){
  //   LHS.makeMaybe();
  //   return;
  // }
  if (V1->comparisonSlt(V2)){
    if (V2->comparisonSle(V1))
      LHS.makeMaybe();   
    else
      LHS.makeTrue();   // must be true
  }
  else
    LHS.makeFalse();    // must be false
}

/// Compare if V1 is (unsigned) less or equal than V2 and store the
/// result in LHS as a Boolean value.
void comparisonUleInst(TBool &LHS, AbstractValue* V1, AbstractValue *V2){ 
  if (V1->comparisonUle(V2)){
    if (V2->comparisonUlt(V1))  
      LHS.makeMaybe();   
    else LHS.makeTrue();   // must be true
  }
  else
    LHS.makeFalse();    // must be false
}

/// Compare if V1 is (unsigned) less than V2 and store the result in
/// LHS as a Boolean value.
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

/// Return true if the meet between V1 and V2 is empty.
bool IsMeetEmpty(AbstractValue *V1,AbstractValue* V2){
  if (V1->isConstant() && V2->isConstant())
    return (!V1->isEqual(V2));
  else{
    if (!V1->isConstant()){
      AbstractValue *Meet = V1->clone();
      Meet->meet(V1,V2);
      return Meet->isBot();
    }
    else{      
      AbstractValue *Meet = V2->clone();
      Meet->meet(V1,V2);
      return Meet->isBot();
    }
  }
}


///  Execute a comparison instruction and store the result: "must
///  true", "must false", or "maybe" in the abstract value of the lhs
///  which must be a TBool object.
void Fixpoint::visitComparisonInst(ICmpInst &I){

  DEBUG(dbgs() << "Comparison instruction: " << I << "\n");
  if (!isTrackedCondFlag(&I))
    return;

  // May swap operands of I: don't do lookups using ClonedI as a base
  // pointer !!
  ICmpInst* ClonedI = normalizeCmpInst(I);    
  // Make sure we make a copy here
  TBool *LHS = new TBool(*TrackedCondFlags.lookup(&I));

  //////////////////////////////////////////////////////////////////////
  // The operands of the ICmpInst could be actually anything. E.g.,
  // 
  // %tmp37 = icmp ult double* %table.0, getelementptr inbounds ([544
  // x double]* @decwin, i32 0, i32 528) 
  //
  // Here the operands are not in ValMap. Thus, we cannot raise an
  // exception in that case. Instead, we just make "maybe" the lhs of
  // the instruction.
  //////////////////////////////////////////////////////////////////////
  AbstractBlock *AbsBB      = BasicBlockToAbstractBlock[I.getParent()];
  assert(AbsBB);
  MapValToAbstractTy ValMap = AbsBB->getValMap();

  if (AbstractValue *Op1 = Lookup(ValMap, ClonedI->getOperand(0), false)){
    if (AbstractValue *Op2 = Lookup(ValMap, ClonedI->getOperand(1), false)){      
      if (Op1->isBot() || Op2->isBot()){
	LHS->makeBottom();
	goto END;
      }
      if (Op1->IsTop() || Op2->IsTop()){
	// Here is one of the operands is top we just say maybe.
	LHS->makeMaybe();
	goto END;
      }
      // Cloned has been already normalized
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
	assert( false &&"ERROR: uncovered comparison operator");
      }  
      goto END;
    }
  }
  // If this point is reachable is because either V1 or v2 were not
  // found in ValMap.
  LHS->makeMaybe();

 END:  
  delete ClonedI;      
  DEBUG(dbgs() << "\t[RESULT]");
  DEBUG(LHS->print(dbgs()));
  DEBUG(dbgs() << "\n");          
  updateCondFlag(I,LHS);
}

/// We perform logical operations (and, or, xor) on 1-bit variables.
/// We use three-valued logic.
void Fixpoint::visitBooleanLogicalInst(Instruction &I){
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
	  assert(false && "Wrong instruction in visitBooleanLogicalInst");
	}	
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
  assert(false && "All operands must be Boolean flags that are being tracked");
}


////////////////////////////////////////////////////////////////////////////
///  Widening 
////////////////////////////////////////////////////////////////////////////

/// Return true iff widening needs to be applied.
bool Fixpoint::Widen(Instruction* I, unsigned NumChanges){
  return ( (WideningLimit > 0) && 
	    WideningPoints.count(I) &&
	   (NumChanges >= WideningLimit));
}    

///  This procedure is vital for the termination of the analysis since
///  it decides which points must be widen so that the analysis can
///  terminate. If we miss a point then we are in trouble.  We
///  consider mainly for widening points phi nodes that are in
///  destination blocks of backedges (arc whose tail dominates its
///  head).  Moreover, we also consider some load instructions done in
///  the destination block of backedges. In particular, where global
///  variables of interest are involved.
void Fixpoint::addTrackedWideningPoints(Function * F){
  if (WideningLimit > 0){    
    SmallVector<std::pair<const BasicBlock*,const BasicBlock*>, 32> BackEdges;
    FindFunctionBackedges(*F, BackEdges);    
    // DestBackEdgeBB - Set of destination blocks of backedges
    SmallPtrSet<const BasicBlock*,16> DestBackEdgeBB;
    typedef SmallVector<std::pair<const BasicBlock*,const BasicBlock*>, 32>::iterator It;
    for (It I = BackEdges.begin(),E = BackEdges.end(); I != E; ++I){
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


/////////////////////////////////////////////////////////////////////
// Stats utilities
/////////////////////////////////////////////////////////////////////

void Fixpoint::gatherStats(){
  // Iterate over all functions defined in the module.
  for (Module::iterator F = M->begin(), E=M->end() ; F != E; ++F){
    if (Utilities::IsTrackableFunction(F)){
      for (Function::iterator 
	     BB = F->begin(), EE = F->end(); BB != EE; ++BB){
	DenseMap<BasicBlock*, AbstractBlock*>::iterator It = 
	  BasicBlockToAbstractBlock.find(BB);
	if (It == BasicBlockToAbstractBlock.end())
	  NumOfUnreachable++;
      else
	It->second->stats();
      } // end for    
    }
  }
}

/////////////////////////////////////////////////////////////////////
// Printing utililties
/////////////////////////////////////////////////////////////////////

void Fixpoint::printResultsGlobals(raw_ostream &Out){
  dbgs () <<"\n===-------------------------------------------------------------------------===\n" ;
  dbgs () << "                 Analysis Results for global variables \n" ;
  dbgs () <<"===-------------------------------------------------------------------------===\n" ;      
  // Iterate over all global variables of interest defined in the module
  for (Module::global_iterator 
	 Gv = M->global_begin(), E = M->global_end();  Gv != E; ++Gv){
    if (TrackedGlobals.count(Gv)){
      GlobalValMap[Gv]->print(Out);
      Out << "\n";
    }
  }
  Out << "\n";
}


void Fixpoint::printResultsFunction(Function *F, raw_ostream &Out){
  if (Utilities::IsTrackableFunction(F)){

    dbgs () <<"\n===-------------------------------------------------------------------------===\n" ;
    dbgs () << "                 Analysis Results for " << F->getName() << "\n" ;
    dbgs () << "                 (Only local variables are displayed) \n" ;
    dbgs () <<"===-------------------------------------------------------------------------===\n" ;      
    
    // Iterate over each basic block.
    for (Function::iterator 
	   BB = F->begin(), EE = F->end(); BB != EE; ++BB){
      DenseMap<BasicBlock*, AbstractBlock*>::iterator It = 
	BasicBlockToAbstractBlock.find(BB);
      if (It == BasicBlockToAbstractBlock.end()){
	Out << "Block " << BB->getName() << " is unreachable!\n";
      }
      else
	It->second->print(Out);
    } // end for
    
    // Boolean flags
    // for (DenseMap<Value*,TBool*>::iterator I=TrackedCondFlags.begin(), E=TrackedCondFlags.end(); I!=E;++I){
    //   if (VST->lookup(I->first->getName()))
    //     Out << " " << I->first->getName() << "=" << I->second->getValue() << "; ";
    // }
  }
}

/// Print the results of the analysis 
void Fixpoint::printResults(raw_ostream &Out){
  // printResultsGlobals(Out);
  // Iterate over all functions defined in the module.
  for (Module::iterator F = M->begin(), E=M->end() ; F != E; ++F)
    printResultsFunction(F,Out);
}

void printValueInfo(Value *v, Function *F){      
  if (Argument *Arg = dyn_cast<Argument>(v))
    dbgs() << F->getName() << "." << Arg->getParent()->getName() 
	   << "." << Arg->getName() 
	   << " type(" << *Arg->getType() << ")\n";
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
	// else{
	//   dbgs() << Inst->getParent()->getName() << "#anonymous" 
	// 	 << " type(" << *Inst->getType() << ")\n";
	// }
      }
    }
  }
}

void printUsersInst(Value *I,SmallPtrSet<BasicBlock*, 16> BBExecutable, 
		    bool OnlyExecutable,
		    DenseMap<Value*, filter_users *> TrackedFilterUsers){ 
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
  if (filter_users * Users = TrackedFilterUsers[I]){ 
    for(filter_users::iterator 
	  UI = Users->begin(),UE = Users->end() ; UI != UE; ++UI){
      if (Instruction * U = dyn_cast<Instruction>(*UI)){
	if (OnlyExecutable){
	  if (BBExecutable.count(U->getParent())) 
	    dbgs() << "\t" << *U << " ;; extra user due to filter.\n";
	}
	else 
	  dbgs() << "\t" << *U << " ;; extra user due to filter.\n";
      } 
    } // end for
  }
}
   
void printTrackedRecursiveFunctions(SmallPtrSet<Function*, 16> TRF){
  dbgs() << "Recursive functions \n";
  for (SmallPtrSet<Function*, 16>::iterator 
	 I=TRF.begin(), E=TRF.end(); I != E; ++I){        
    Function* F = *I;    
    dbgs ()  << "\t" << F->getName() << "\n";
  }
}

void printFilterUsers(DenseMap<Value*,filter_users*> TrackedFilterUsers){
  for(DenseMap<Value*,filter_users*>::iterator 
	I=TrackedFilterUsers.begin(), E= TrackedFilterUsers.end();
      I!=E; ++I){
    dbgs() <<  I->first->getName() << " uses : {";
    filter_users * Users = I->second;
	for(filter_users::iterator 
	      UI= Users->begin(), UE= Users->end(); UI !=UE; ++UI)
	  dbgs() << (*UI)->getName() << ";";      
	dbgs() << "}\n";
  }
}


