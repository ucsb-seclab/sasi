// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef __UTILITIES_H__
#define __UTILITIES_H__
///////////////////////////////////////////////////////////////////////////////
/// \file  Utils.h.
///        Some common utilities 
///////////////////////////////////////////////////////////////////////////////

#include "llvm/Value.h"
#include "llvm/Constants.h"
#include "llvm/Type.h"
#include "llvm/Module.h"
#include "llvm/Instructions.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"

#include <set>

using namespace llvm;

namespace unimelb {

  class Utilities{
  public:
    /// If the type t is an integer then return its
    /// width (in Width) and return true. Otherwise, return false.
    static bool getIntegerWidth(const Type * t, unsigned &Width){      
      if (t->isIntegerTy(1))  Width=1;
      if (t->isIntegerTy(8))  Width=8;
      if (t->isIntegerTy(16)) Width=16;
      if (t->isIntegerTy(32)) Width=32;
      if (t->isIntegerTy(64)) Width=64;
      
      if ( (t->isIntegerTy(1))  || (t->isIntegerTy(8))  || 
	   (t->isIntegerTy(16)) || (t->isIntegerTy(32)) || (t->isIntegerTy(64)) ) 
	return true;
      else
	return false;      
    }
  
    /// If the value v is a pointer to an integer
    /// then return width of value (in Width) and return
    /// true. Otherwise, return false.
    static bool getPointerIntWidth(const Value *v, unsigned &Width){
      if (v->getType()->isPointerTy()){
	Type*  BasicT = v->getType()->getContainedType(0);
	return getIntegerWidth(BasicT,Width);
      }
      else
	return false;
    }
    
    /// Return true if the value v has a supported
    /// type. In that case, return also its type t and width.
    static bool getTypeAndWidth(Value *v, Type *&t, unsigned &Width){
      if (getIntegerWidth(v->getType(),Width)){
	t = v->getType();
	return true;
      }
      // Global variables are represented in LLVM IR as pointers
      if (GlobalVariable * gv = dyn_cast<GlobalVariable>(v)){
	if (getPointerIntWidth(gv,Width)){
	  t = gv->getType()->getContainedType(0);
	  return true;
	}
      }
      return false;
    }     


    /// Return true if the address of the value may be taken.
    /// Borrowed from SCCP.cpp.
    static bool AddressIsTaken(const GlobalValue *GV) {
      GV->removeDeadConstantUsers();
      
      for (Value::const_use_iterator UI = GV->use_begin(), E = GV->use_end();
	   UI != E; ++UI) {
	const User *U = *UI;
	if (const StoreInst *SI = dyn_cast<StoreInst>(U)) {
	  if (SI->getOperand(0) == GV || SI->isVolatile())
	    return true;  // Storing addr of GV.
	} else if (isa<InvokeInst>(U) || isa<CallInst>(U)) {
	  // Make sure we are calling the function, not passing the address.
	  ImmutableCallSite CS(cast<Instruction>(U));
	  if (!CS.isCallee(UI))
	    return true;
	} else if (const LoadInst *LI = dyn_cast<LoadInst>(U)) {
	  if (LI->isVolatile())
	    return true;
	} else if (isa<BlockAddress>(U)) {
	  // blockaddress doesn't take the address of the function, it takes addr
	  // of label.
	} else {
	  return true;
	}
      }
      return false;
    }

    /// Return true if the analysis will consider F.
    static bool IsTrackableFunction(const Function *F){  
      if (F == NULL)          return false;

      if (F->isDeclaration()) return false;

      if (F->hasFnAttr(Attribute::AlwaysInline)) return false;

      if (!F->mayBeOverridden()){       
	// Since we do not perform inter-procedural analysis and we
	// always analyze each function assuming worst-case scenario the analysis
	// of a function is sound even if its address can be taken.
	// The numbers reported in the APLAS paper were obtained by
	// ignoring functions whose addresses can be taken.
	/* if (AddressIsTaken(F)){ */
	/*   //DEBUG(dbgs() << "\t" << F->getName() << " is passed as a pointer.\n"); */
	/*   return false; */
	/* }   */
	/* else */
	return (!AddressIsTaken(F));
      }
      else{
	//DEBUG(dbgs() << "\t" << F->getName() << " may be overriden.\n");
	dbgs() << "\t" << F->getName() << " may be overriden.\n";
	return false;
      }
    }

    
    static inline int64_t convertConstantIntToint64_t(ConstantInt *C){
      return C->getValue().getSExtValue();
    }

    ///  Create abstract value for each constant in the program.
    static void
    addTrackedIntegerConstants(Function *F, bool IsAllSigned, 
			       std::vector<std::pair<Value*,ConstantInt*> > &NewAbsVals){

      LLVMContext *ctx = &F->getContext();

      
      for (inst_iterator I = inst_begin(F), E=inst_end(F) ; I != E; ++I){
	for (User::op_iterator i = I->op_begin(), e = I->op_end(); i != e; ++i){
	  if (ConstantInt *C = dyn_cast<ConstantInt>(*i)){
	    unsigned width;
	    if (Utilities::getIntegerWidth(C->getType(),width)){
	      if (width <= 64) // Programs like susan has i288 constants!
		NewAbsVals.push_back(std::make_pair(&*C,C));
	    }
	  }
	  else{	
	    if (Constant *CC = dyn_cast<Constant>(*i)){
	      if (CC->isNullValue()){ // "null"
		// Create an integer constant with value 0 and width 32 bits.
		ConstantInt * Zero = 
		  cast<ConstantInt>(ConstantInt::get(Type::getInt32Ty(*ctx), 
						     0, 
						     IsAllSigned));
		NewAbsVals.push_back(std::make_pair(&*CC,Zero));
	      }
	    }
	  }
	} // end for
      } // end for      
    }

    ///  Record constants that appear in the program
    static void recordIntegerConstants(Function *F, std::set<int64_t> &ConstSet){
      //////////////////////////////////////////////////////////////////////////////
      // We also insert the maximum and minimum values for unsigned and
      // signed versions for common widths (8,16, and 32). This is
      // important for domains like WrappedRangeLattice in order to avoid
      // widening to jump too much when the intervals wraparound.
      //////////////////////////////////////////////////////////////////////////////
      int64_t umin8  = APInt::getMinValue(8).getZExtValue();
      int64_t smin8  = APInt::getSignedMinValue(8).getSExtValue();
      int64_t umax8  = APInt::getMaxValue(8).getZExtValue();
      int64_t smax8  = APInt::getSignedMaxValue(8).getSExtValue();
      int64_t umin16 = APInt::getMinValue(16).getZExtValue();
      int64_t smin16 = APInt::getSignedMinValue(16).getSExtValue();
      int64_t umax16 = APInt::getMaxValue(16).getZExtValue();
      int64_t smax16 = APInt::getSignedMaxValue(16).getSExtValue();
      int64_t umin32 = APInt::getMinValue(32).getZExtValue();
      int64_t smin32 = APInt::getSignedMinValue(32).getSExtValue();
      int64_t umax32 = APInt::getMaxValue(32).getZExtValue();
      int64_t smax32 = APInt::getSignedMaxValue(32).getSExtValue();

      ConstSet.insert(umin8);  ConstSet.insert(umax8); 
      ConstSet.insert(smin8);  ConstSet.insert(smax8);
      ConstSet.insert(umin16); ConstSet.insert(umax16);
      ConstSet.insert(smin16); ConstSet.insert(smax16); 
      ConstSet.insert(umin32); ConstSet.insert(umax32);
      ConstSet.insert(smin32); ConstSet.insert(smax32);
      
      for (inst_iterator I = inst_begin(F), E=inst_end(F) ; I != E; ++I){
	for (User::op_iterator i = I->op_begin(), e = I->op_end(); i != e; ++i){
	  if (ConstantInt *C = dyn_cast<ConstantInt>(*i)){
	    unsigned width;
	    if (Utilities::getIntegerWidth(C->getType(),width)){
	      if (width <= 64){ // Programs like susan has i288 constants!
		ConstSet.insert(convertConstantIntToint64_t(C)-1);
		ConstSet.insert(convertConstantIntToint64_t(C));
		ConstSet.insert(convertConstantIntToint64_t(C)+1);
	      }
	    }
	  }
	} // end for
      } // end for      
    }

    // For debugging
    static void printIntConstants(const std::set<int64_t> &JumpSet){
      dbgs() << "PROGRAM INTEGER CONSTANTS:{ ";
      for(std::set<int64_t>::iterator i= JumpSet.begin(), e = JumpSet.end(); i!=e; ++i)
	dbgs () << *i << ";";
      dbgs() << "}\n";
    }
    static void printIntConstants(const std::vector<int64_t> &JumpSet){
      dbgs() << "PROGRAM INTEGER CONSTANTS:{ ";
      for(unsigned int i=0; i < JumpSet.size(); i++)
	dbgs () << JumpSet[i] << ";";
      dbgs() << "}\n";
    }

    // Lexicographical order
    static bool Lex_LessThan_Comp(int64_t x,int64_t y) {
      bool IsPositive_x, IsPositive_y;
      (x < 0 ? IsPositive_x=false:IsPositive_x=true);
      (y < 0 ? IsPositive_y=false:IsPositive_y=true);
      
      if (IsPositive_x &&  !IsPositive_y) return true;
      else if ( !IsPositive_x && IsPositive_y) return false;
      else return x < y;
    }
  

  };
} // End namespace
#endif
