# Isabelle-LLVM with Time

Isabelle-LLVM with Time is a verification framework for simultaneous verification of correctness and worst-case
complexity of practically competitive algorithms. It utilizes a stepwise refinement approach, targeting LLVM as backend.
It is based on the [Isabelle/HOL](https://isabelle.in.tum.de) theorem prover.

## Prerequisites
  * To compile the LLVM code: Working installation of [LLVM](http://releases.llvm.org/) version >= 6.0.0.
  * To re-check the proofs: Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) 
    with the [Archive of Formal Proofs](https://www.isa-afp.org) installed 
    as as described on [https://www.isa-afp.org/using.shtml](https://www.isa-afp.org/using.shtml). 
    We require version = Isabelle-2020, which, at the time of writing, is the current version.

## Compiling and running benchmarks
  To compile and run the benchmarks

    cd benchmarks/sorting
    make run

    
## Re-Checking the Proofs
  To re-check the proofs, run

      cd thys 
      isabelle build -D.
      
  Here, <code>isabelle</isabelle> must refer to <code>/your/path/to/Isabelle2020/bin/isabelle</code> from your Isabelle installation.
  This will invoke Isabelle to check all proofs and re-generate the exported code.

