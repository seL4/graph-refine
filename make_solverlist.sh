#! /bin/bash
set -ex

# This script is a dodgy reimplementation of what
# the TV bamboo test does.

export L4V_ARCH="${L4V_ARCH:?Must set L4V_ARCH}"

export TV_ROOT="${TV_ROOT:?Must set TV_ROOT.

TV_ROOT should point to a sync'd and init'd verification checkout, i.e. it
should point to the parent directory of l4v, graph-refine, HOL4, etc.}"

export TV_ROOT="$(realpath "${TV_ROOT}")"

# Set up SMT solvers
cd $TV_ROOT
if [ ! -f smtsolvers/done ]; then
    mkdir smtsolvers -p || true
    cd smtsolvers

    cd ${TV_ROOT}/smtsolvers

    echo CVC4: online: $(pwd)/cvc4-1.5-3/x86_64-linux/cvc4 \
        --incremental --lang smt --tlimit=5000 > solverlist
    echo SONOLAR: offline: $(pwd)/sonolar-2014-12-04-x86_64-linux/bin/sonolar \
        --input-format=smtlib2 >> solverlist
    echo CVC4: offline: $(pwd)/cvc4-1.5-3/x86_64-linux/cvc4 --lang smt >> solverlist
    echo SONOLAR-word8: offline: $(pwd)/sonolar-2014-12-04-x86_64-linux/bin/sonolar \
        --input-format=smtlib2 >> solverlist

    case $L4V_ARCH in
        ARM) echo config: mem_mode = 32 >> solverlist ;;
        RISCV64) echo config: mem_mode = 8 >> solverlist ;;
        *) echo ERROR: L4V_ARCH should be ARM or RISCV64 >> solverlist ;;
    esac

    touch done
fi
