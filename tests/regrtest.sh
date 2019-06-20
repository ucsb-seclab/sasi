#!/bin/bash

######################################################################
# Script to run a bunch of tests and compare with expected results
# Usage: ./regrtest.sh
######################################################################

CMMD="../tools/run.sh"
#PASS="-compare-range-analyses"
PASS="-compare-strided-range-analyses"
TEST_DIR="../tests"

# global counters
success=0
fails=0
dies=0

#######################################################################
# Usage: getAndCheckStats output expBetterWrapped expBetterUnwrapped
#######################################################################
# where output is a filename to dump the analysis results.
#       expBetterWrapped is the number of intervals for which wrapped
#                        analysis is expected to be more precise.
#       expBetterUnwrapped is the number of intervals for which unwrapped
#                        analysis is expected to be more precise.
#######################################################################
function getAndCheckStats {
    file=$1
    expBetterWrapped=$2
    expBetterUnwrapped=$3
    if grep "Summary results" $file > /dev/null ; then
	x=`grep -ie "wrapped < unwrapped"  $file | sed 's@\(.*\):\(.*\)(tolerance=0)@\2@g'` 
	y=`grep -ie "unwrapped < wrapped"  $file | sed 's@\(.*\):\(.*\)// should be 0.@\2@g'` 
	if [ $x -eq $expBetterWrapped ] && [ $y -eq $expBetterUnwrapped ]; then
	    echo "test passed."
 	    success=$[ $success + 1]	
	else
	    echo "test failed: unexpected result in $file."
 	    fails=$[ $fails + 1]	
	fi
    else 
	echo "test failed: unexpected error on ${file}." 
 	dies=$[ $dies + 1]	
    fi
}


echo "RUNNING REGRESSION TESTS ... "

echo "Running t1.c"
$CMMD $TEST_DIR/t1.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log1
getAndCheckStats $TEST_DIR/log1 0 0
echo "Running t2.c"
$CMMD $TEST_DIR/t2.c $PASS -widening 3 -narrowing 1 -inline 300 >& $TEST_DIR/log2
getAndCheckStats $TEST_DIR/log2 0 0
echo "Running t3.c"
$CMMD $TEST_DIR/t3.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log3
getAndCheckStats $TEST_DIR/log3 0 0
echo "Running t4.c"
$CMMD $TEST_DIR/t4.c $PASS -widening 3 -narrowing 1 -instcombine >& $TEST_DIR/log4
getAndCheckStats $TEST_DIR/log4 0 0
echo "Running t5.c"
$CMMD $TEST_DIR/t5.c $PASS -widening 3 -narrowing 1 -instcombine -inline 300 >& $TEST_DIR/log5
getAndCheckStats $TEST_DIR/log5 0 0
echo "Running t6.c"
$CMMD $TEST_DIR/t6.c $PASS -widening 3 -narrowing 1 -inline 300 >& $TEST_DIR/log6
getAndCheckStats $TEST_DIR/log6 0 0
echo "Running t7.c"
$CMMD $TEST_DIR/t7.c $PASS -widening 3 -narrowing 1 -inline 300 >& $TEST_DIR/log7
getAndCheckStats $TEST_DIR/log7 0 0
echo "Running t8.c"
$CMMD $TEST_DIR/t8.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log8 
getAndCheckStats $TEST_DIR/log8 0 0
echo "Running t9.c"
$CMMD $TEST_DIR/t9.c $PASS -widening 4 -narrowing 1 >& $TEST_DIR/log9
getAndCheckStats $TEST_DIR/log9 0 0
echo "Running t10.c"
$CMMD $TEST_DIR/t10.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t11.c"
$CMMD $TEST_DIR/t11.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t12.c"
$CMMD $TEST_DIR/t12.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t13.c"
$CMMD $TEST_DIR/t13.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t14.c"
$CMMD $TEST_DIR/t14.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t15.c"
$CMMD $TEST_DIR/t15.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t16.c"
$CMMD $TEST_DIR/t16.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t17.c"
$CMMD $TEST_DIR/t17.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t18.c"
$CMMD $TEST_DIR/t18.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t19.c"
$CMMD $TEST_DIR/t19.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0

echo "Running t20.c"
$CMMD $TEST_DIR/t20.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t21.c"
$CMMD $TEST_DIR/t21.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t22.c"
$CMMD $TEST_DIR/t22.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t23.c"
$CMMD $TEST_DIR/t23.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 2 0
echo "Running t24.c"
$CMMD $TEST_DIR/t24.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0

echo "Running t31.c"
$CMMD $TEST_DIR/t31.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t32.c"
$CMMD $TEST_DIR/t32.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t33.c"
$CMMD $TEST_DIR/t33.c $PASS -widening 3 -narrowing 1 -instcombine >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 3 0

echo "Running modulo.c"
$CMMD $TEST_DIR/modulo.c $PASS -widening 7 -narrowing 1 -instcombine >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 6 0

echo "Running t40.c"
$CMMD $TEST_DIR/t40.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 3 0

echo "Running t50.c"
$CMMD $TEST_DIR/t50.c $PASS -widening 3 -narrowing 2 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 4 0
echo "Running t51.c"
$CMMD $TEST_DIR/t51.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 3 0
echo "Running t52.c"
$CMMD $TEST_DIR/t52.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t53.c"
$CMMD $TEST_DIR/t53.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 1 0
echo "Running t54.c"
$CMMD $TEST_DIR/t54.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 5 0

echo "Running t60.c"
$CMMD $TEST_DIR/t60.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t61.c"
$CMMD $TEST_DIR/t61.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0
echo "Running t62.c"
$CMMD $TEST_DIR/t62.c $PASS -widening 3 -narrowing 1 >& $TEST_DIR/log
getAndCheckStats $TEST_DIR/log 0 0

echo "DONE. "

echo "==============================================="
echo "               Test summary                    "
echo "==============================================="
echo "Number of successful tests             : $success" 
echo "Number of failed  tests                : $fails" 
echo "Number of tests with unexpected errors : $dies" 

