#!/bin/bash

#
# Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# set -ex

export L4V_ARCH=RISCV64
export L4V_FEATURES=MCS
export CONFIG_OPTIMISATION_LEVEL='-O1'

# set USE_SONOLAR to true if you're a non-commerical user or if you have a SONOLAR license, it will make the proofs a lot faster
if [ "$USE_SONOLAR" != true ]; then
    echo "USE_SONOLAR not set"
    export USE_SONOLAR=false
fi
echo "USE_SONOLAR is set to $USE_SONOLAR"

# we find the binary verification root directory by recursively walking up the tree
BV_ROOT="$PWD"
while [ "$BV_ROOT" != "/" -a ! -d "$BV_ROOT/graph-refine" ]; do
  BV_ROOT=$(dirname "$BV_ROOT")
done
if [ "$BV_ROOT" = "/" ]; then
  echo "Could not find the binary verification repo root directory."
  echo "Make sure to run this script from a fresh 'repo' checkout."
  exit 1
fi

echo "Found binary verification root directory:"
echo "$BV_ROOT"

echo "Checking HOL4 status..."
# make sure that HOL4 has been built
if [ ! -f "$BV_ROOT/HOL4/HOL4.done" ]; then
    echo "HOL4 needs to be built."
    bash "$BV_ROOT/graph-refine/scripts/setup-HOL4.sh" && touch "$BV_ROOT/HOL4/HOL4.done"
fi
echo "HOL4 is built."

echo "Checking SMT solvers..."
if [ ! -f "$BV_ROOT/solvers/solvers.done" ]; then
    mkdir "$BV_ROOT/solvers" -p || true
    pushd "$BV_ROOT/solvers"

    # CVC4 1.8
    echo "Installing solver CVC4..."
    wget -q https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
    mkdir "$BV_ROOT/solvers/cvc4" -p || true
    mv cvc4-1.8-x86_64-linux-opt "$BV_ROOT/solvers/cvc4/"
    chmod +x "$BV_ROOT/solvers/cvc4/cvc4-1.8-x86_64-linux-opt"

    # SONOLAR 2014-12-04
    if $USE_SONOLAR; then
        echo "Installing solver SONOLAR..."
        wget -q http://www.informatik.uni-bremen.de/agbs/florian/sonolar/sonolar-2014-12-04-x86_64-linux.tar.gz
        cp "$BV_ROOT/graph-refine/seL4-example/sonolar-2014-12-04-x86_64-linux.sha" .
        if ! shasum -q -c sonolar-2014-12-04-x86_64-linux.sha; then
            echo "SONOLAR checksum did not match"
            exit 1
        fi;
        tar xzf sonolar-2014-12-04-x86_64-linux.tar.gz
    fi

    # Yices2 2.6.2
    echo "Installing solver Yices2..."
    wget -q https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz
    tar xzf yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz

    touch "$BV_ROOT/solvers/solvers.done"
    popd
fi
echo "SMT Solvers are installed."

echo "Checking solverlist..."
if [ ! -f "$BV_ROOT/graph-refine/.solverlist" ]; then
    SOLVERLIST_TEMPLATE="$BV_ROOT/graph-refine/seL4-example/solverlist-template"
    if $USE_SONOLAR; then
        SOLVERLIST_TEMPLATE="$BV_ROOT/graph-refine/seL4-example/solverlist-template-nc"
    fi
    cp "$SOLVERLIST_TEMPLATE" "$BV_ROOT/graph-refine/.solverlist"
    sed -i "s#SOLVERS_ROOT#$BV_ROOT/solvers#g" "$BV_ROOT/graph-refine/.solverlist"
fi
echo "Solverlist working."

echo "Proving..."
pushd "$BV_ROOT/graph-refine/seL4-example/"
make report
echo "Done."
popd
