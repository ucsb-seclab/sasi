// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __ABSTRACT_BLOCK_H__
#define __ABSTRACT_BLOCK_H__
//////////////////////////////////////////////////////////////////////////////
/// \file AbstractBlock.h
/// This class represent an abstract state.
//////////////////////////////////////////////////////////////////////////////

#include "AbstractValue.h"
#include "Support/Utils.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/ADT/Statistic.h"

#include <map>

STATISTIC(DominanceQueries    , "Number of dominance queries");
STATISTIC(DominanceCacheHits  , "Number of dominance cache hits");

//STATISTIC(TotalAbsVal         , "Total number of tracked abstract values");
//STATISTIC(NonTrivialAbsVal    , "Total number of non-top tracked abstract values");

using namespace std;
using namespace llvm;

#define DEBUG_TYPE "RangeAnalysis"

namespace unimelb {

  typedef DenseMap<Value *, AbstractValue*> MapValToAbstractTy;
  typedef SmallPtrSet<Value *, 16>  filter_users;

  /// Class to represent a constraint.
  class BinaryConstraint{
  public:
    /// Constructor of the class.
    BinaryConstraint(unsigned _pred, Value* _Op1, Value* _Op2): pred(_pred), Op1(_Op1), Op2(_Op2){}
    /// Destructor of the class.
    ~BinaryConstraint(){}

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
      return ( (pred == C->getPred()) && (Op1 == C->getOperand(0)) && (Op2 == C->getOperand(1)));
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
	    default: assert(false);
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

  struct BinaryConstraintCmp {
    bool operator()(const BinaryConstraint *C1, const BinaryConstraint *C2) const {
      // syntactic equivalence.
      return ( C1->getPred()     == C2->getPred() &&
      	       C1->getOperand(0) == C2->getOperand(0) &&
      	       C1->getOperand(1) == C2->getOperand(1));
    }
  };


  typedef std::set<BinaryConstraint*, BinaryConstraintCmp> BinaryConstraintSetTy;
  typedef DenseMap<Value* , BinaryConstraintSetTy * > FiltersTy;
  typedef std::map<std::pair<BasicBlock*,BasicBlock*>, bool> DominatorCacheTy;
  
  /// This class maps a basic block to its abstract state. An abstract
  /// state is a map of Value's to AbstractValue's.
  class AbstractBlock{
  public:
    /// Constructor of the class.
    AbstractBlock(BasicBlock * _B, MapValToAbstractTy _valMap): B(_B), valMap(_valMap){}
    /// Destructor of the class.
    ~AbstractBlock(){
      for(MapValToAbstractTy::iterator I = valMap.begin(), E = valMap.end(); I!=E; ++I)
	delete I->second;
      // FIXME: raises a double free exception
      /* for(FiltersTy::iterator I = filters.begin(),E = filters.end(); I!=E; ++I){ */
      /* 	for(BinaryConstraintSetTy::iterator II= I->second->begin(), EE = I->second->end(); II != EE; ++II){ */
      /* 	  BinaryConstraint * C = *II; */
      /* 	  if(C) delete C; */
      /* 	} */
      /* } */
    }
    /// Give access to the map.
    MapValToAbstractTy getValMap() const { return valMap;}
    /// Give access to the basic block.
    BasicBlock* getBasicBlock(){ return B; }
    /// Give access to the filters.
    FiltersTy getFilters(){ return filters;}
    /// Give access to the users of the filter V. It can be null.
    /// Return the set of defined and used variables in the block B.
    const SmallPtrSet<Value*,32> DefinedAndUsedVariables(BasicBlock *B) const{
      SmallPtrSet<Value*, 32>  vars;
      for (BasicBlock::iterator I = B->begin(), E= B->end(); I != E; ++I){	
	if (Value * lhs = dyn_cast<Value>(I))
	  vars.insert(lhs);

	if (ReturnInst *RI = dyn_cast<ReturnInst>(I)){
	  if (RI->getNumOperands() == 0) continue;  
	  else{
	    if (!isa<ConstantInt>(RI->getOperand(0)))
	      vars.insert(RI->getOperand(0));
	  }
	}       
	else if (PHINode *PN = dyn_cast<PHINode>(I)){
	  for (unsigned i=0, num_vals=PN->getNumIncomingValues(); i != num_vals;i++)
	    if (!isa<ConstantInt>(PN->getIncomingValue(i)))
	      vars.insert(PN->getIncomingValue(i));
	}	
	else if (SelectInst *SelI = dyn_cast<SelectInst>(I)){
	  if (!isa<ConstantInt>(SelI->getTrueValue()))
	    vars.insert(SelI->getTrueValue());
	  if (!isa<ConstantInt>(SelI->getFalseValue()))
	    vars.insert(SelI->getFalseValue());
	}
	else if (ICmpInst *ICmpI = dyn_cast<ICmpInst>(I)){
	  if (!isa<ConstantInt>(ICmpI->getOperand(0)))
	    vars.insert(ICmpI->getOperand(0));
	  if (!isa<ConstantInt>(ICmpI->getOperand(1)))
	    vars.insert(ICmpI->getOperand(1));
	}
	else if (BinaryOperator *BinOpI = dyn_cast<BinaryOperator>(I)){
	  if (!isa<ConstantInt>(BinOpI->getOperand(0)))
	    vars.insert(BinOpI->getOperand(0));
	  if (!isa<ConstantInt>(BinOpI->getOperand(1)))
	    vars.insert(BinOpI->getOperand(1));
	}
	// make sure we do not miss any relevant instruction!
      }     
      return vars;
    }

    /// Print the abstract block. Display only defined and used
    /// variables in the block.
    void print(raw_ostream &Out) const {
     const SmallPtrSet<Value*,32> Vars = DefinedAndUsedVariables(B);
      Out << "Block " << B->getName() << ":{"; 
      for(SmallPtrSet<Value*,32>::iterator I = Vars.begin(), E = Vars.end(); I != E; ++I){
	if (const AbstractValue * V = getValMap()[*I]){
	  if (!V->isBot()){ 
	    // We run -instnamer pass before everything to make sure each
	    // value has a name.
	    assert(V->getValue()->hasName());
	    V->print(Out);
	    Out << "; ";
	  }
	}
      }
      Out << "}\n"; 
    }

    /// Gather some quick stats
    void stats() const {
     // const SmallPtrSet<Value*,32> Vars = DefinedAndUsedVariables(B);
     //  for(SmallPtrSet<Value*,32>::iterator I = Vars.begin(), E = Vars.end(); I != E; ++I){
     // 	if (isa<GlobalVariable>(*I) || isa<ConstantInt>(*I))
     // 	  continue;   
     // 	if (const AbstractValue * V = getValMap()[*I]){
     // 	  TotalAbsVal++;
     //// countForStats() is not longer a method from AbstractValue
     // 	  if (V->countForStats())
     // 	    NonTrivialAbsVal++;
     // 	}
     //  }
    }

    /// Update the map.
    void updateValMap(MapValToAbstractTy map){ valMap = map; }
    
    /// Recursively traverse I which is the instruction that
    /// defines the lhs of the branch instruction BI. The lhs of BI
    /// is a Boolean flag. From I we extract the constraints whose evaluation
    /// decides whether the flag is true or false.
    void visitInstrToFilter(BranchInst * BI, ICmpInst*    I, 
			    DominatorTree*, DominatorCacheTy &,
			    DenseMap<Value*, filter_users*> &);
    void visitInstrToFilter(BranchInst * BI, SelectInst*  I, 
			    DominatorTree*, DominatorCacheTy &,
			    DenseMap<Value*, filter_users*> &);			    
    void visitInstrToFilter(BranchInst * BI, Instruction* I, DenseMap<Value*,TBool*>, 
			    DominatorTree*, DominatorCacheTy &,
			    DenseMap<Value*, filter_users*> &); 
    void visitBoolInstrToFilter(bool, Instruction*, DenseMap<Value*,TBool*>, 
				DenseMap<Value*, filter_users*> &);
    /// Auxiliary methods to generate and store constraints using the
    /// class BinaryConstraint.
    void genConstraint(unsigned, Value*, Value*, DenseMap<Value*, filter_users*> &);
    void genConstraintsfromICmpInst(Instruction *, bool, DenseMap<Value*, filter_users*> &);
    void genConstraintsfromBoolInst(Value *,DenseMap<Value*,TBool*>, DenseMap<Value*, filter_users*> &);

    /// To build users chains. This is needed because our analysis may
    /// modify variables that are not in SSA. Because of that, we need
    /// to re-build  machinery that LLVM already provides for SSA values
    /// (e.g., user chains).
    void markFilterUser(DenseMap<Value*,filter_users*> & Users, Value *V, Value *User){
      if (!isa<ConstantInt>(V)){
	if (filter_users * S = Users[V]){
	  S->insert(User);
	  Users[V] = S;
	}
	else{
	  S->insert(User);
	  // Users.insert(std::make_pair(V,S)); // this does not work
	  Users[V] = new filter_users();
	}
      }      
    }

  private:
    BasicBlock                     *B;  //!< Basic block.
    MapValToAbstractTy         valMap;  //!< Map basic block values to its abstract counterparts.
    FiltersTy filters; //!< Constraints from branches that may refine the abstract value.

    /// Copy constructor of the class.
    /// We do not allow to copy.
    AbstractBlock(const AbstractBlock * AbsB);

  };

  /// Return true if block Then dominates block B or false if block
  /// Else dominates B. Use a cache to reuse queries since the method
  /// dominates is not constant.
  inline bool DominateBlock(DominatorTree *DT, DominatorCacheTy &DC,
			    BasicBlock *B1, BasicBlock *B2){

   DominatorCacheTy::iterator It = DC.find(std::make_pair(B1,B2));
   if( It != DC.end()){
     DominanceCacheHits++;
     return It->second;
   }
   else{
     DomTreeNode *  D_B1 = DT->getNode(B1);
     DomTreeNode *  D_B2 = DT->getNode(B2);
     DominanceQueries++;
     bool f = DT->dominates(D_B1,D_B2);
     DC.insert(std::make_pair(std::make_pair(B1,B2),f));
     return f;
   }
  }
  
  inline unsigned DecideWhetherFiltering(DominatorTree *DT, 
					 DominatorCacheTy &DC,
					 BasicBlock *Predec, 
					 BasicBlock *Then, BasicBlock *Else,
					 BasicBlock *Curr){
    // Pre: Terminator of Predec is a conditional instrution whose two
    // successors are Then and Else.
    if (DominateBlock(DT, DC, Predec, Curr )){
      if      (Then == Curr) return 1; 
      else if (Else == Curr) return 2; 
      else if (DominateBlock(DT, DC, Then,Curr)) return 1;
      else if (DominateBlock(DT, DC, Else,Curr)) return 2;
    }
    // Either Predec does not dominate Curr or 
    // Predec dominates Curr but its successors (Then and Else) do
    // no dominate Curr. This is common if Curr contains a phi node.
    return 0;
  }


  /// Filter the current abstract value by using information from a
  /// comparison instruction.
  void AbstractBlock::visitInstrToFilter(BranchInst *BI, ICmpInst* CI, 
					 DominatorTree* DT, DominatorCacheTy &DC,
					 DenseMap<Value*, filter_users*> &Users){	  

    unsigned which = 
      DecideWhetherFiltering(DT, DC,
			     BI->getParent(), BI->getSuccessor(0), BI->getSuccessor(1), getBasicBlock()); 
    switch(which){
    case 1:  // then
      genConstraint(CI->getSignedPredicate(), 
		    CI->getOperand(0), CI->getOperand(1), Users);  
      break;
    case 2:  // else
      genConstraint(CI->getInversePredicate(CI->getSignedPredicate()), 
		    CI->getOperand(0), CI->getOperand(1), Users);
      break;
    default: // we do not filter here.
      return;
    }
  }
     
  
  /// Filter the current abstract value by using information from a
  /// select instruction.
  void AbstractBlock::visitInstrToFilter(BranchInst *BI, SelectInst* SI, 
					 DominatorTree* DT, DominatorCacheTy &DC,
					 DenseMap<Value*, filter_users*> &Users){
    unsigned which = 
      DecideWhetherFiltering(DT, DC,
			     BI->getParent(), BI->getSuccessor(0), BI->getSuccessor(1), getBasicBlock()); 
    bool selectCondFlag;
    switch(which){
    case 1:  // then
      selectCondFlag=true;
      break;
    case 2:  // else
      selectCondFlag=false;
      break;
    default: // we do not filter here.
      return;
    }

    // temporary
    assert(false);

    if (selectCondFlag){
      // Here we know that the condition and the first operand of
      // SelectInst must be true. 
      if (Instruction * I = dyn_cast<Instruction>(SI->getCondition()))
	genConstraintsfromICmpInst(I, false, Users);  // false means not negate the condition
      if (Instruction * I = dyn_cast<Instruction>(SI->getTrueValue()))
	genConstraintsfromICmpInst(I, false, Users ); // false means not negate the condition
    }
    else{
      // Here we know that the condition is false and the second operand
      // of SelectInst must be true.
      if (Instruction * I = dyn_cast<Instruction>(SI->getCondition()))
	genConstraintsfromICmpInst(I, true, Users);   // true means negate the condition
      if (Instruction * I = dyn_cast<Instruction>(SI->getFalseValue()))
	genConstraintsfromICmpInst(I, false, Users); // false means not negate the condition   
    }  
  }

  /// Filter the current abstract value by using information from a
  /// And/Or/Xor instruction of type i1.
  void AbstractBlock::visitInstrToFilter(BranchInst * BI, Instruction* I,
					 DenseMap<Value*,TBool*> TrackedCondFlags,
					 DominatorTree* DT, DominatorCacheTy &DC,
					 DenseMap<Value*, filter_users*> &Users){

    // Precondition: I is an instruction of type i1 and And, Or, or Xor
    unsigned which = 
      DecideWhetherFiltering(DT, DC,
			     BI->getParent(), BI->getSuccessor(0), BI->getSuccessor(1), getBasicBlock()); 
    bool CondFlag;
    switch(which){
    case 1:  // then
      CondFlag=true;
      break;
    case 2:  // else
      CondFlag=false;
      break;
    default: // we do not filter here.
      return;
    }

    visitBoolInstrToFilter(CondFlag, I, TrackedCondFlags, Users);
  }

  void AbstractBlock::visitBoolInstrToFilter(bool Outcome, 
					     Instruction* I,
					     DenseMap<Value*,TBool*> TrackedCondFlags,
					     DenseMap<Value*, filter_users*> &Users){
    switch(I->getOpcode()){
    case Instruction::And:
      if (Outcome){ 
	// here we know that the two operands of the And instruction
	// must be true (very strong claim)
	if (Instruction * Op1 = dyn_cast<Instruction>(I->getOperand(0))){
	  // false means not negate the condition
	  genConstraintsfromICmpInst(Op1, false, Users);  
	}
	if (Instruction * Op2 = dyn_cast<Instruction>(I->getOperand(1))){
	  // false means not negate the condition
	  genConstraintsfromICmpInst(Op2, false, Users);  
	}
      }
      else{
	//////////////////////////////////////////////////////////////////////
	// However, here the two operands may be false or only one may
	// be false. Thus, we cannot make such a strong claim as in the
	// previous case although still we can do something:
	//
	// - if either operand is false then we can propagate that.
	// - if an operand is top of course we do nothing
	// - if an operand is true but the other top we do also nothing.
	//
	// Thus, we can still propagate constraints only if the operand
	// is false.
	//////////////////////////////////////////////////////////////////////
	DenseMap<Value*,TBool*>::iterator It1, It2;
	It1 = TrackedCondFlags.find(I->getOperand(0));	
	if (It1 != TrackedCondFlags.end()){
	  if (It1->second->isFalse())
	    genConstraintsfromBoolInst(I->getOperand(0),TrackedCondFlags, Users);
	}
	It2 = TrackedCondFlags.find(I->getOperand(1));	
	if (It2 != TrackedCondFlags.end()){
	  if (It2->second->isFalse())
	    genConstraintsfromBoolInst(I->getOperand(1),TrackedCondFlags, Users);
	}
      }
      break;    
    case Instruction::Or:
      if (!Outcome){ 
	// here we know that the two operands of the Or instruction must
	// be false (strong claim!)
	if (Instruction * Op1 = dyn_cast<Instruction>(I->getOperand(0))){
	  // true means that we negate the condition
	  genConstraintsfromICmpInst(Op1, true, Users);  
	}
	if (Instruction * Op2 = dyn_cast<Instruction>(I->getOperand(1))){
	  // true means that we negate the condition
	  genConstraintsfromICmpInst(Op2, true, Users);  
	}
      }
      else{
	// However, here the two operands may be true or at least one
	// is true.  Thus, we cannot make such a strong claim as in
	// the previous case although still we can do something if the
	// operand is true.
	DenseMap<Value*,TBool*>::iterator It1, It2;
	It1 = TrackedCondFlags.find(I->getOperand(0));	
	if (It1 != TrackedCondFlags.end()){
	  if (It1->second->isTrue())
	    genConstraintsfromBoolInst(I->getOperand(0), TrackedCondFlags, Users);
	}
	It2 = TrackedCondFlags.find(I->getOperand(1));	
	if (It2 != TrackedCondFlags.end()){
	  if (It2->second->isTrue())
	    genConstraintsfromBoolInst(I->getOperand(1), TrackedCondFlags, Users);
	}
      }
      break;    
    case Instruction::Xor:
      assert(false && "TODO: implement!");
      break;
    default:
      assert(false && "Unexpected case in visitInstrToFilter");
    }
  }


  /// Generate the constraint Op1 'pred' Op2 and store it in the
  /// abstract block.
  void AbstractBlock::genConstraint(unsigned pred, Value *Op1, Value *Op2,
				    DenseMap<Value*, filter_users*> &Users){    

    BinaryConstraint * C = new BinaryConstraint(pred,Op1,Op2);
    if (!C->isConstantOperand(0)){
      FiltersTy::iterator It = filters.find(Op1);
      if (It != filters.end()){
	BinaryConstraintSetTy *Rhs  = It->second;
	assert(Rhs);
	Rhs->insert(C);
	filters[Op1]=Rhs;
	DEBUG(dbgs() << "\n\t" << B->getName() << ":";
	      C->print();
	      dbgs() << "\n");
      }
      else{
	BinaryConstraintSetTy * Rhs = new BinaryConstraintSetTy();
	Rhs->insert(C);
	filters.insert(std::make_pair(Op1, Rhs));
	DEBUG(dbgs() << "\n\t" << B->getName() << ":";
	      C->print();
	      dbgs() << "\n");
	
      }
    }

    if (!C->isConstantOperand(1)){
      FiltersTy::iterator It = filters.find(Op2);
      if (It != filters.end()){
	BinaryConstraintSetTy *Rhs = It->second;
	assert(Rhs);
	Rhs->insert(C);
	filters[Op2]=Rhs;
	DEBUG(dbgs() << "\n\t" << B->getName() << ":";
	      C->print();
	      dbgs() << "\n");
      }
      else{
	BinaryConstraintSetTy *Rhs = new BinaryConstraintSetTy();
	Rhs->insert(C);
	filters.insert(std::make_pair(Op2, Rhs));
	DEBUG(dbgs() << "\n\t" << B->getName() << ":";
	      C->print();
	      dbgs() << "\n");
      }
    }

    // Build user chains: op1 is an user of op2 and viceversa.
    // If Op1
    if (!C->isConstantOperand(0) && !C->isConstantOperand(1)){
      markFilterUser(Users, Op1, Op2);
      markFilterUser(Users, Op2, Op1);
    }
  }

  /// Generate constraints from a ICmpInst instruction. This method is
  /// recursive in case the operands are nested ICmpInst instructions.
  void AbstractBlock::genConstraintsfromICmpInst(Instruction *I, bool Negate,
						 DenseMap<Value*, filter_users*> &Users){

    if (ICmpInst * CI = dyn_cast<ICmpInst>(I)){
      unsigned pred;
      if (Negate)
	pred = CI->getInversePredicate(CI->getSignedPredicate());
      else
	pred = CI->getSignedPredicate();

      genConstraint(pred, CI->getOperand(0),  CI->getOperand(1), Users);
    }
    // This does not make sense: it will go through the instructions
    // but without checking the kind of instruction
    /* else{ */
    /*   // Recurse	   */
    /*   if (Instruction *I1 = dyn_cast<Instruction>(I->getOperand(0))) */
    /* 	genConstraintsfromICmpInst(I1, Negate, Users); */
    /*   if (Instruction *I2 = dyn_cast<Instruction>(I->getOperand(1))) */
    /* 	genConstraintsfromICmpInst(I2, Negate, Users); */
    /* } */
  }

  /// Generate constraints from an And, Or, or Xor instruction of
  /// i1. This method is recursive in case the operands are nested
  /// And/Or/Xor instructions.
  void AbstractBlock::genConstraintsfromBoolInst(Value * BoolInstOper,
						 DenseMap<Value*,TBool*> TrackedCondFlags,
						 DenseMap<Value*, filter_users*> &Users){
    
    // BoolInstOper is an operand of an And, Or, or Xor instruction.
    // TrackedCondFlags keeps track of all Values of type i1    
    if (Instruction * Operand = dyn_cast<Instruction>(BoolInstOper)){
      DenseMap<Value*,TBool*>::iterator It = TrackedCondFlags.find(BoolInstOper);	
      if (It != TrackedCondFlags.end()){
	TBool * CFlag = It->second;
	// If we know that the flag is not top then we can refine the
	// abstract state of the current BasicBlock
	if (!CFlag->isMaybe()){
	  if (isa<ICmpInst>(Operand)){
	    // Base case
	    genConstraintsfromICmpInst(Operand, !(CFlag->isTrue()), Users);
	  }
	  // This does not make sense: it will go through the instructions
	  // but without checking the kind of instruction
	  /* else{ */
	  /*   // Recurse	   */
	  /*   if (Instruction *I1 = dyn_cast<Instruction>(Operand->getOperand(0))) */
	  /*     genConstraintsfromBoolInst(I1, TrackedCondFlags, Users); */
	  /*   if (Instruction *I2 = dyn_cast<Instruction>(Operand->getOperand(1))) */
	  /*     genConstraintsfromBoolInst(I2, TrackedCondFlags, Users); */
	  /* } */
	}
      }
    }
  }


} // End llvm namespace

#endif
