#!/bin/bash

DIR=${PWD##*/}

if test ! -e thys.txt; then
  echo Rebuilding theory list
  isabelle build -n -D thys -d contrib/Imperative_HOL_Time -l | grep "^  $PWD/thys/" | sed -re "s|  $PWD/||" > thys.txt
  echo Done
fi


rm -f dist.tar dist.tar.gz dist.tgz

cd ..
tar -cf "$DIR/dist.tar" --exclude-ignore-recursive=.distignore --exclude="$DIR/thys/*" --exclude="$DIR/dist.tar" --transform "s|^$DIR|isabelle-llvm-time|" "$DIR"
tar -rf "$DIR/dist.tar" -T <(sed -re "s|^|$DIR/|" $DIR/thys.txt) --transform "s|^$DIR|isabelle-llvm-time|"
cd - >/dev/null
gzip dist.tar
mv dist.tar.gz dist.tgz
