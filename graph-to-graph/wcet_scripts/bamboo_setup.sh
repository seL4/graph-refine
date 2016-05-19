#!/bin/bash
# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

#used for setting up HOL4 on our internal setup

# Fetch directory this script is stored in.
DIR="$(cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd)"
echo $DIR
SETUP_ROOT=${DIR}/../../../

#setup HOL4
cd $SETUP_ROOT/HOL4
echo 'val polymllibdir= "'$POLY_LIB_DIR'";' > ./tools-poly/poly-includes.ML
echo 'configuring HOL4'
$POLY < tools/smart-configure.sml
echo 'HOL4 configured, building ...'
$SETUP_ROOT/HOL4/bin/build

