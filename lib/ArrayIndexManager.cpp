#include "ArrayIndexManager.h"
#include "llvm/Operator.h"

using namespace NEWEVAL;

std::map<const Function*, std::map<const Value*, std::set<const Value*> > > ArrayIndexClassifier::allFuncIndexGroups;

bool ArrayIndexClassifier::setupFunction(Function* targetFunction) {
    if(!ArrayIndexClassifier::hasArrayGroups(targetFunction)) {
        for (Function::iterator BB = targetFunction->begin(), EE = targetFunction->end(); BB != EE; ++BB) {
            // Iterate over each instruction.
            for (BasicBlock::iterator I = BB->begin(), IE = BB->end(); I != IE; ++I) { 
                Instruction *currInstr = &(*I);
                // is the current instruction GetElementPtr?
                if(dyn_cast<GetElementPtrInst>(currInstr)) {
                    GetElementPtrInst *currGepInstr = dyn_cast<GetElementPtrInst>(currInstr);
                    GEPOperator *gep = dyn_cast<GEPOperator>(currGepInstr->getPointerOperand());
                    Value *targetOp = NULL;
                    if(gep && gep->getNumOperands() > 0 && gep->getPointerOperand()) {
                        targetOp = gep->getPointerOperand();
                    } else {
                        targetOp = currGepInstr->getPointerOperand();
                    }
                    // get the pointer operand.
                    targetOp = targetOp->stripPointerCasts();
                    // is this local?
                    if(ArrayIndexClassifier::isValidPointerSrc(targetOp)) {
                        // and this is array access operation.
                        if(currGepInstr->getNumOperands() == 2) {
                            Value *indexVal = currGepInstr->getOperand(1)->stripPointerCasts();
                            ArrayIndexClassifier::allFuncIndexGroups[targetFunction][targetOp].insert(indexVal);
                        }
                    }                       
                    
                }
                
            }
        }
        return true;
    }
    return false;
}

bool ArrayIndexClassifier::isValidPointerSrc(Value *currVal) {
    if(dyn_cast<AllocaInst>(currVal) || dyn_cast<GlobalVariable>(currVal)) {
            return true;
    }

    if(dyn_cast<GlobalValue>(currVal) || dyn_cast<Constant>(currVal)) {
        return true;
    }

    CallInst *currCall = dyn_cast<CallInst>(currVal);
    if(currCall != NULL) {
        Function *calledFunction = currCall->getCalledFunction();
        if(calledFunction != NULL && calledFunction->hasName()) {
            if(calledFunction->getName().str() == "malloc" || calledFunction->getName().str() == "calloc") {
                return true;
            }
        }
    }
    return false;
}


bool ArrayIndexClassifier::hasArrayGroups(const Function* targetFunction) {
    return ArrayIndexClassifier::allFuncIndexGroups.find(targetFunction) != ArrayIndexClassifier::allFuncIndexGroups.end();
}

std::map<const Value*, std::set<const Value*> >& ArrayIndexClassifier::getFunctionArrayGroups(const Function *targetFunction) {
    return ArrayIndexClassifier::allFuncIndexGroups[targetFunction];
}

AllFuncValueGrTy& ArrayIndexClassifier::getAllFuncValueGroup() {
    return ArrayIndexClassifier::allFuncIndexGroups;
}