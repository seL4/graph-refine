#! /bin/bash

# * Copyright 2018, Data61
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(Data61_BSD)

HOL4_DIR=$(ls -d HOL4 ../HOL4 ../../HOL4 2> /dev/null | head -n 1)
if [[ -e $HOL4_DIR ]]
then
  HOL4_DIR=$(readlink -f $HOL4_DIR)
  echo "Setting up HOL4 in $HOL4_DIR"
else
  echo "No HOL4 found"
  exit 1
fi

POLY_DIR=$HOL4_DIR/polyml
POLY=$POLY_DIR/deploy/bin/poly
if [[ -e $POLY ]]
then
  echo PolyML already built.
elif [[ -e $POLY_DIR/configure ]]
then
  echo Building PolyML in $POLY_DIR
  echo '  (tracing build progress to poly_output.txt)'
  OUT=$(readlink -f poly_output.txt)
  pushd $POLY_DIR
  echo '  (configuring)'
  (./configure --prefix=$POLY_DIR/deploy) &> $OUT
  echo '  (building)'
  (make && make install) &>> $OUT
  if [[ -e $POLY ]]
  then
    echo Built PolyML
  else
    echo Failed to build PolyML
    echo see poly_output.txt
    exit 1
  fi
elif [[ -e $POLY_DIR ]]
then
  echo Missing PolyML source in $POLY_DIR
  exit 1
else
  echo No PolyML dir $POLY_DIR
  exit 1
fi

# this script cleans any previous build of HOL4
# this is needed when pulling in new revisions to the base system
OUT=$(readlink -f hol4_output.txt)
echo output is $OUT
pushd $HOL4_DIR

echo Cleaning HOL4 build in $HOL4_DIR
git clean -fdX -e polyml &> /dev/null

echo Building HOL4 now.
echo '  (tracing build progress to hol4_output.txt)'
echo '  (configuring)'
$POLY < tools-poly/smart-configure.sml &> $OUT
popd

if [[ ! -e $HOL4_DIR/bin/build ]]
then
  echo Failed to configure HOL4.
  echo see hol4_output.txt
  exit 1
fi

echo '  (building)'
PATH=$HOL4_DIR/bin:$PATH build &>> $OUT

if ( tail $OUT | grep 'built successfully' )
then
  echo 'Built HOL4.'
else
  echo Failed to build HOL4
  echo see hol4_output.txt
  exit 1
fi

