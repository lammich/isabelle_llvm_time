# ![Isabelle-LLVM with Time Logo](logo_200.png) Isabelle-LLVM with Time

Isabelle-LLVM with Time is a verification framework for simultaneous verification of correctness and worst-case
complexity of practically competitive algorithms. It utilizes a stepwise refinement approach, targeting LLVM as backend.
It is based on the [Isabelle/HOL](https://isabelle.in.tum.de) theorem prover.

## Getting Started
  You can [browse the theories](Isabelle_LLVM_Time/) or [download](dist.tgz) the files.

  Warning: the .thy files in the download are best viewed with the [Isabelle/HOL](https://isabelle.in.tum.de) IDE.

### Starting Points for Browsing
  Here are some default starting points for browsing the theories

#### Introsort Case Study
  [Introsort](Isabelle_LLVM_Time/Sorting_Introsort.html)

#### Isabelle-LLVM
  [Shallow Embedding of LLVM Semantics](Isabelle_LLVM_Time/LLVM_Shallow.html)


## Prerequisites
  * To compile the LLVM code: Working installation of [LLVM](http://releases.llvm.org/) version >= 6.0.0.
  * To re-check the proofs: Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) 
    with the [Archive of Formal Proofs](https://www.isa-afp.org) installed 
    as as described on [https://www.isa-afp.org/using.shtml](https://www.isa-afp.org/using.shtml). 
    We require version = Isabelle-2020, which, at the time of writing, is the current version.

## Compiling and running benchmarks
  To compile and run the benchmarks

    cd benchmarks\sorting
    make run

  This will run the sorting benchmarks.
  Warning: We have only tested this on a Linux x86_64 platform so far. 
  We do not (yet) know how LLVM will digest our code on other platforms.
    
## Re-Checking the Proofs
  To re-check the proofs, run

      cd thys 
      isabelle build -D . -d ../contrib/Imperative_HOL_Time/

  Here, <code>isabelle</isabelle> must refer to <code>/your/path/to/Isabelle2020/bin/isabelle</code> from your Isabelle installation.
  This will invoke Isabelle to check all proofs and re-generate the exported code.

## Talks and Publications


### Isabelle-LLVM without Time
  [IJCAR'2020 Paper](paper_IJCAR2020.pdf) [Slides](slides_IJCAR2020.pdf)

  [ITP'2019 Paper](paper_ITP2019.pdf) [Slides](slides_ITP2019.pdf)


  [Mar 2020 Talk in Enschede](enschede2020.pdf)

  [Dec 2019 Talk in Rennes](rennes2019.pdf)

