#ifndef __ARRAY_INDEX_MANAGER_H__
#define __ARRAY_INDEX_MANAGER_H__

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
#include <set>
#include <map>

using namespace std;
using namespace llvm;

namespace NEWEVAL {
    typedef std::map<const Function*, std::map<const Value*, std::set<const Value*> > > AllFuncValueGrTy;
    typedef std::map<const Value*, std::set<const Value*> > ValueGroupTy;
    class ArrayIndexClassifier {
        private:
            static AllFuncValueGrTy allFuncIndexGroups;
            static bool isValidPointerSrc(Value *currVal);
        public:
            /***
             *
             */
            static bool setupFunction(Function* targetFunction);

            static bool hasArrayGroups(const Function* targetFunction);

            static std::map<const Value*, std::set<const Value*> >& getFunctionArrayGroups(const Function *targetFunction);

            static AllFuncValueGrTy& getAllFuncValueGroup();
            

    };
}

#endif