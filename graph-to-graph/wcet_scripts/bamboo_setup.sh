#!/bin/bash
#
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

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
./bin/build
