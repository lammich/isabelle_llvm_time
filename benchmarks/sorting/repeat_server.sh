#!/bin/bash 
echo -n '# '; date 
echo -n '# '; uname -a 
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 std::sort random-boolean 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::sort random-boolean 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 std::sort rev-sorted 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::sort rev-sorted 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 std::sort almost-sorted-.1 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::sort almost-sorted-.1 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 std::sort sorted 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::sort sorted 100000000 10

