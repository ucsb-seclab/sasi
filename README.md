# Signedness-Agnostic Strided Interval Analysis 

This project provides the implementation of a new interval analysis,
called Signed Agnostic Strided interval analysis. It is implemented in C++ using the
LLVM framework, and currently, it has only support for C programs
which are translated to LLVM IR (Intermediate Representation) via
Clang.

This implementation is based on Wrapped Intervals (https://github.com/regehr/wrapped-intervals).

# Installation 

## Checkout and installation of LLVM and Clang 

1. Get the required tools
   - See http://llvm.org/docs/GettingStarted.html#requirements

2. Checkout LLVM:
   - ```LLVM_ROOT=any_directory_you_like```
   - ```cd $LLVM_ROOT```
   - ```svn co -r 139364 http://llvm.org/svn/llvm-project/llvm/trunk llvm``` 

3. Checkout Clang (C/C++ frontend):
   - ```cd $LLVM_ROOT/llvm/tools```
   - ```svn co -r 139290 http://llvm.org/svn/llvm-project/cfe/trunk clang```

4. Build LLVM and Clang:

   - ```cd $LLVM_ROOT/llvm```
   - ```mkdir build``` 
   - ```cd build```
   - ```../configure -enable-optimized=no CC="gcc -m32" CXX="g++ -m32"```
   - ```make``` 
   This builds both LLVM and Clang for debug mode.

## Checkout and installation of the Signed-Agnostic Strided Interval Analysis 

- ```git clone git@github.com:ucsb-seclab/sasi.git```
- ``` cd sasi```
- ```. setenv`
- ```./configure --with-llvmsrc=$LLVM_ROOT/llvm --with-llvmobj=$LLVM_ROOT/llvm/build```
- ```./make```
- ```cd ./docs && make```  (optional)
- Change ```$CLANG_PATH``` and ```$OPT_PATH``` in the ```tools/run.sh``` script


# Usage 

```
tools/run.sh prog[.c|.bc]  Pass [options] 

Pass is the pass that we want to run: 
  -strided-wrapped-range-analysis      Strided Fixed-Width Wrapped Integer Range Analysis (SASI)	
  -wrapped-range-analysis      fixed-width wrapped interval analysis
  -range-analysis                fixed-width classical interval analysis
    options:
      -widening n                n is the widening threshold (0: no widening)
      -narrowing n               n is the number of narrowing iterations (0: no narrowing)
      -alias                     by default, -no-aa which always return maybe. If enabled 
                                 then -basic-aa and -globalsmodref-aa are run to be more precise
                                 with global variables.
      -enable-optimizations      enable LLVM optimizations
      -inline n                  inline function calls whenever possible if the size of 
                                 the function is less than n. (0: no inlining). 
                                 A reasonable threshold n is, e.g., 255.
      -instcombine               remove redundant instructions.
                                 It can improve precision by removing problematic casting 
                                 instructions among many other things.
      -insert-ioc-traps          Compile .c program with -fcatch-undefined-ansic-behavior 
                                 which generates IOC trap blocks.  
                                 Note: clang version must support -fcatch-undefined-ansic-behavior    
                       
  general options:
    -help                          print this message
    -stats                         print stats
    -time                          print LLVM time passes
    -dot-cfg                       print .dot file of the LLVM IR
    -debug                         print debugging messages
```

# Running Benchmarks
1. Extract all benchmarks in the folder benchmark_evaluation/spec_benchmarks/
2. Running:
```
cd benchmark_evaluation
python benchmark_config.py
```
