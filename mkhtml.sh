#!/bin/bash

BASEDIR=$PWD

REBUILD=false
UPLOAD=false

while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -r|--rebuild)
    REBUILD=true
    ;;
    -u|--upload)
    UPLOAD=true
    ;;
    *)
    echo "Unknown command line argument $1"        # unknown option
    exit 1
    ;;
esac
shift # past argument or value
done



if $REBUILD; then
  isabelle build -v -D thys -d contrib/Imperative_HOL_Time
  ./mkdist.sh
fi


rm -rf html
mkdir -p html
cp -a html.in/* html/

ISABELLE_BROWSER_INFO=$(isabelle getenv ISABELLE_BROWSER_INFO | sed -re 's/.*=//')

cp -a $ISABELLE_BROWSER_INFO/Unsorted/Isabelle_LLVM_Time html/
cp index.md html/
cp dist.tgz html/
cp LICENSE html/
cp etc/logo/logo_200.png html/

pandoc -V pagetitle="Isabelle LLVM with Time" -s index.md > html/index.html


if $UPLOAD; then
  LOCAL_DEST=~/devel/www21-lammich/isabelle_llvm_time
  rm -rf $LOCAL_DEST
  cp -a html $LOCAL_DEST
  cd $LOCAL_DEST
  echo ADD
  hg add .
  echo COMMIT
  hg commit -m "Automatic update of Isabelle-LLVM" .
  echo PUSH
  hg push
  echo DONE
  cd $BASEDIR
fi


