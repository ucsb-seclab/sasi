// Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and
//          Peter J. Stuckey.
// The University of Melbourne 2012.
#ifndef TBOOL_H
#define TBOOL_H
///////////////////////////////////////////////////////////////////////////////
/// \file TBool.h 
///       Quick class to reason about three-valued logic
///////////////////////////////////////////////////////////////////////////////

#include "llvm/Support/raw_ostream.h"
#include <string>

namespace unimelb{

  class TBool{ 
  public:
    /// Constructor of the class
    TBool(): flag(TUNDEF){}
    /// Destructor of the class
    ~TBool(){}
    
    /// Return true if the Boolean value is true.
    inline bool isTrue()  { return (flag == TTRUE);}
    /// Return true if the Boolean value is false.
    inline bool isFalse() { return (flag == TFALSE); }
    /// Return true if the Boolean value is undefined.
    inline bool isMaybe() { return (flag == TUNDEF); } 
    /// Return true if the Boolean value is bottom.
    inline bool isBottom(){ return (flag == TBOT); } 
    /// Convert the Boolean value to a string.
    inline std::string getValue(){
      if (flag == TTRUE)  return "true";
      if (flag == TFALSE) return "false";
      if (flag == TBOT)   return "bottom";
      return "*";      
    }
    /// Print the Boolean value.
    inline void print(llvm::raw_ostream &Out){
      Out << getValue();
    }
    
    /// Return if this and newF are equal.
    inline bool isEqual(TBool * newF){
      if ( (isTrue()  && newF->isTrue())  || 
	   (isFalse() && newF->isFalse()) ||
	   (isMaybe() && newF->isMaybe()) ||
	   (isBottom() && newF->isBottom()))
	return true;
      return false;
    }
    
    /// Make this true.
    inline void makeTrue()  {flag=TTRUE;}
    /// Make this false.
    inline void makeFalse() {flag=TFALSE;}
    /// Make this undefined.
    inline void makeMaybe() {flag=TUNDEF;}
    /// Make this bottom.
    inline void makeBottom(){flag=TBOT;}
    
    /// And operation between F1 and F2.
    ///
    /// \verbatim
    ///  And| 0  1 U    
    ///  -------------  
    ///  0 | 0  0  0    
    ///  1 | 0  1  U    
    ///  U | 0  U  U    
    /// \endverbatim
    void And(TBool * F1, TBool * F2){
      if (F1->isBottom() || F2->isBottom()){
	makeBottom();
	return;
      }
      
      if (F1->isFalse()) 
	makeFalse();
      else{
      if (F1->isTrue()){
	if (F2->isFalse())
	  makeFalse();
	else{
	  if (F2->isTrue()) 
	    makeTrue();
	  else 
	    makeMaybe();
	}
      }
      else{
	if (F2->isFalse()) 
	  makeFalse();
	else 
	  makeMaybe();
      }
      }      
    }
    
    /// Or operation between F1 and F2.
    ///
    /// \verbatim
    ///  Or| 0  1 U 
    ///  -----------
    ///  0 | 0  1  U
    ///  1 | 1  1  1
    ///  U | U  1  U
    /// \endverbatim
    void Or(TBool * F1, TBool * F2){
      if (F1->isBottom() || F2->isBottom()){
	makeBottom();
	return;
      }

      if (F1->isTrue()) 
	makeTrue();
      else{
	if (F1->isFalse()){
	  if (F2->isFalse()) 
	    makeFalse();
	  else{
	    if (F2->isTrue()) 
	      makeTrue();
	    else 
	      makeMaybe();
	  }
	}
	else{
	  if (F2->isTrue()) 
	    makeTrue();
	  else 
	    makeMaybe();
	}
      }
    }

    /// Xor operation between F1 and F2.
    ///
    /// \verbatim
    ///  Xor| 0  1  U
    /// -------------      
    ///  0 | 0  1  U
    ///  1 | 1  0  U
    ///  U | U  U  U  
    /// \endverbatim
    void Xor(TBool * F1, TBool * F2){
      if (F1->isBottom() || F2->isBottom()){
	makeBottom();
	return;
      }

      if (F1->isMaybe() || F2->isMaybe())
	makeMaybe();
      else{
	if ( (F1->isTrue() && F2->isFalse()) || 
	     (F1->isFalse() && F2->isTrue()))
	  makeTrue();
	else
	  makeFalse();
      }
    }

  private:
    typedef enum {TFALSE = 0, TTRUE = 1, TUNDEF=2, TBOT=3} TBoolValue;
    TBoolValue flag;

  };
} // end namespace
#endif /*TBOOL_H*/
