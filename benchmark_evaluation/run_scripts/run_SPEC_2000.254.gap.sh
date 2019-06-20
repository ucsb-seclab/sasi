#!/bin/bash

#=======================================================================#
# Change the following variables for clang and opt
#=======================================================================#
###
# Another version with 32-bits
###
COMP_MODE="Debug+Asserts"
LLVM_BIN="$LLVM_ROOT/llvm/build/$COMP_MODE/bin"
CLANG_PATH=$LLVM_BIN
OPT_PATH=$LLVM_BIN
###
# for 3.0 version with 32-bits 
# Use this version if -run-ioc
###
# COMP_MODE="Debug"
# LLVM_BIN="$HOME/SvnReps/UNIMELB/trunk/verification/domains/code/wrapped-intervals/.llvm-3.0.ioc/build/$COMP_MODE/bin"
# CLANG_PATH=$LLVM_BIN
# OPT_PATH=$LLVM_BIN
#=======================================================================#

get_dir() {
	pushd "$1" > /dev/null
	pwd
	popd > /dev/null
}

usage() {
cat <<EOF

Authors: Jorge. A Navas, Peter Schachte, Harald Sondergaard, and 
         Peter J. Stuckey.
The University of Melbourne 2012.

Usage: $0  prog[.c|.bc]  Pass [options] 

Pass is the pass that we want to run: 
  -strided-wrapped-range-analysis      Strided Fixed-Width Wrapped Integer Range Analysis	
  -wrapped-range-analysis      fixed-width wrapped interval analysis
  -range-analysis              fixed-width classical interval analysis
    options:
      -widening n              n is the widening threshold (0: no widening)
      -narrowing n             n is the number of narrowing iterations (0: no narrowing)
      -alias                   by default, -no-aa which always return maybe. If enabled 
                               then -basic-aa and -globalsmodref-aa are run to be more 
                               precise with global variables.
      -enable-optimizations    enable LLVM optimizations
      -inline n                inline function calls whenever possible if the size of 
                               the function is less than n. (0: no inlining). 
                               A reasonable threshold n is, e.g., 255.
      -instcombine             remove redundant instructions.
                               It can improve precision by removing problematic casting 
                               instructions among many other things.

      -only-function fname     Analyze only fname rather than the whole program.            
      -numfuncs n              Shortcut to analyze the first n functions of the program.

      -insert-ioc-traps        Compile .c program with -fcatch-undefined-ansic-behavior
                               which generates IOC trap blocks.
                               Note: clang version must support -fcatch-undefined-ansic-behavior
                                 
  general options:
    -help                      print this message
    -stats                     print stats
    -time                      print LLVM time passes
    -dot-cfg                   print .dot file of the LLVM IR
    -debug                     print debugging messages


EOF
}

if [ $# -eq 0 ]; then
    usage
    exit 2
else
    if [ $# -eq 1 ]; then
	if [ "$1" == "-help" ]; then
	    usage
	    exit 2
	else
	    echo -e "Run with option -help\n"	    
	    exit 2
	fi
    else
	if [ $# -lt 2 ]; then
	    echo -e "ERROR: some input argument is missing\n"
	    usage
	    exit 2
	fi
    fi
fi


# clang 
FRONTEND="$CLANG_PATH/clang "
# llvm opt tool 
OPT="$OPT_PATH/opt"
# clang options
FRONTEND_OPTS=" -DSIZEOF_VOID_P=4 -c -g -O -m32 -ILLVM_BIN=$SASI_ROOT/si_eval/spec_benchmarks/gap4r8/src -ILLVM_BIN=$SASI_ROOT/si_eval/spec_benchmarks/gap4r8/pkg/guava-3.13/src/ctjhai"
FRONTEND_IOC_OPTS=" -O0 -m32 -fcatch-undefined-ansic-behavior "
# libraries that contain my passes
# The directory of this script
SCRIPT_DIR="`get_dir \`dirname "${BASH_SOURCE[0]}"\``"
WRAPPED_PATH="`get_dir $SCRIPT_DIR/..`"
MYLIBRARY_PATH="$SCRIPT_DIR/../../Debug+Asserts/lib"

COMPILE_WITH_IOC=0 
# Input C program
input="$1"
# The pass that we want to run
mypass="$2"
# To dump garbage
out=out.txt

###############################################################
#### Passes that we must run always before our passes.
PRE_MYPASS="-scalarrepl -instnamer -range-transformations -instcount "
# -scalarrepl performs SSA transformation (includes -mem2reg)
# -instnamer makes sure that all variables has a name (debugging purposes). 
# -range-transformations performs all transformations needed by the
#  range analyses.   
###############################################################
# Alias analyses
ALIAS_OPTS=""
###############################################################
# For general options
GENERAL_OPTS=""
###############################################################
# For extra options of my passes
MYPASS_OPTS=""
###############################################################

# Process args
while [ "$3" != "" ]; do
    case "$3" in
	-help)
	    shift
	    usage
	    exit 2
	    ;;	
	-stats)
	    shift
	    GENERAL_OPTS="$GENERAL_OPTS -aa-eval -stats "
	    ;;
	-dot-cfg)
	    shift
	    GENERAL_OPTS="$GENERAL_OPTS -dot-cfg "
	    ;;
	-debug)
	    shift
	    GENERAL_OPTS="$GENERAL_OPTS -debug-only=RangeAnalysis "
#	    GENERAL_OPTS="$GENERAL_OPTS -debug "
	    ;;
	-only-function)
	    shift
	    GENERAL_OPTS="$GENERAL_OPTS -only-function=$3"
	    shift
	    ;;
	-time)
	    shift
	    GENERAL_OPTS="$GENERAL_OPTS -time-passes "
	    ;;
	-widening)
	    shift
	    MYPASS_OPTS="$MYPASS_OPTS -widening=$3"
	    shift
	    ;;
	-narrowing)
	    shift
	    MYPASS_OPTS="$MYPASS_OPTS -narrowing=$3"
	    shift
	    ;;
	-enable-optimizations)
	    shift
	    MYPASS_OPTS="$MYPASS_OPTS -enable-optimizations"
	    ;;
	-alias)
	    shift
	    ALIAS_OPTS="$ALIAS_OPTS -basicaa -globalsmodref-aa"
	    ;;
	-inline)
	    shift
	    MYPASS_OPTS="$MYPASS_OPTS -Inline=$3"
	    shift
	    ;;
	-instcombine)
	    shift
	    MYPASS_OPTS="$MYPASS_OPTS -InstCombine"
	    ;;
	-numfuncs)
	    shift
	    MYPASS_OPTS="$MYPASS_OPTS -numfuncs=$3"
	    shift
	    ;;
	-insert-ioc-traps)
	    shift
	    COMPILE_WITH_IOC=1
	    ;;
	*)
	    echo -e "ERROR: option $3 not recognized.\nExecute $0 -help to see options.\n"
	    exit 2
	    ;;
    esac
done


###################################################################
# Sanity checks
###################################################################

# Function - is $1 installed?
_have() { which "$1" &>/dev/null; }

if ! _have $FRONTEND;  
then
    echo "[run-llvm]: command \"$FRONTEND\" is not found."
    echo "[run-llvm]: add the directory where \"$FRONTEND\" is located to \$PATH."
    exit 0
fi

if ! _have $OPT;  
then
    echo "[run-llvm]: command \"$OPT\" is not found."
    echo "[run-llvm]: add the directory where \"$OPT\" is located to \$PATH."
    exit 0
fi


#######################################################################
# Figure out file paths
#######################################################################

filename=`basename $input`
dirname=`dirname $input`
fileext=${filename##*.}

if [ $fileext == "c" ]; then
    require_compilation=1
    basename_NOSUFFIX=${filename%.c}
else
    if [ $fileext == "bc" ]; then
	require_compilation=0
	basename_NOSUFFIX=${filename%.bc}
    else
	echo -e "[run-llvm] unrecognized file extension (only .c, .bc, or .rbc) \n"
	exit 2
    fi	
fi

basename_C=${basename_NOSUFFIX}.c
basename_BC=${basename_NOSUFFIX}.bc

abspath_C="`cd \"$dirname\" 2>/dev/null && pwd || echo \"$dirname\"`/$basename_C"
abspath_BC="`cd \"$dirname\" 2>/dev/null && pwd || echo \"$dirname\"`/$basename_BC"

#########################################################################
# Run opt tool
#########################################################################

## Here all the passes
MYLIBRARIES="$MYLIBRARIES -load ${MYLIBRARY_PATH}/Fixpoint.so"
MYLIBRARIES="$MYLIBRARIES -load ${MYLIBRARY_PATH}/RangeAnalysis.so"
MYLIBRARIES="$MYLIBRARIES -load ${MYLIBRARY_PATH}/Transformations.so"

# Compile the C program to llvm bytecode
if [ $require_compilation -eq 1 ]; then
    if [ $COMPILE_WITH_IOC -eq 1 ]; then
	$FRONTEND $FRONTEND_IOC_OPTS -w $abspath_C -c -emit-llvm -o $abspath_BC
    else
	$FRONTEND $FRONTEND_OPTS -w $abspath_C -c -emit-llvm -o $abspath_BC
    fi
fi

# Catch some errors ...
if [ "$MYLIBRARIES" == "" ]; then	       
    echo -e "We could not load the libraries\n"
    exit 2
fi
    
if [ -e $abspath_BC ]; then	 
    $OPT $MYLIBRARIES $PRE_MYPASS $ALIAS_OPTS $mypass $MYPASS_OPTS $GENERAL_OPTS $abspath_BC > /dev/null
else
    echo -e "[run-llvm]: .bc file not found.\n"
    exit 2	
fi








	
