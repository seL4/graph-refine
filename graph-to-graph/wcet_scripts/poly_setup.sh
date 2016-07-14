#!/bin/bash

# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

#used for setting up polyml for our internal regression tests

# Fetch directory this script is stored in.
DIR="$(cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd)"
echo $DIR
SETUP_ROOT=${DIR}/../../../
POLY_DIR=$SETUP_ROOT/polyml
POLY=$POLY_DIR/deploy/bin/poly

#setup polyml
mkdir -p $POLY_DIR
POLY_OUT=$POLY_DIR/poly_output.txt
echo 'configuring and installing polyml'
pushd $POLY_DIR
(./configure --prefix=$POLY_DIR/deploy && make && make install) &> $POLY_OUT
popd
if [[ -e $POLY ]]
then
    echo Built PolyML
else
    echo Failed to build PolyML!
fi

