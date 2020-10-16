#!/bin/bash 
echo -n '# '; date 
echo -n '# '; uname -a 
echo '# Repeated b/c difference > 15\% (1884,1516)'
./do_benchmark uint64 std::sort random-boolean 100000000 10
./do_benchmark uint64 isabelle::sort random-boolean 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::sort almost-sorted-10 100000000 10
