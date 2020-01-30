#!/bin/ksh

PF=riscv64-unknown-linux-gnu-
CC="$PF""gcc"
DMP="$PF""objdump"
L4V_ROOT=/home/yshen/work/verificatin/l4v
L4V_ARCH=RISCV64
PARSERPATH="$L4V_ROOT"/tools/c-parser/standalone-parser/c-parser
HOL4_ROOT=/home/yshen/work/verificatin/HOL4
DECOMP_DIR="$HOL_ROOT""/examples/machine-code/graph"
DECOMP="$HOL4_ROOT"/examples/machine-code/graph/decompile.py


echo $PF
echo $CC
echo $DMP
rm kernel/*

mkdir kernel
$CC -march=rv64gc --static -nostdlib  -O1 kernel.c -o kernel.elf
$DMP -D kernel.elf > kernel.elf.rodata
$DMP -dz kernel.elf > kernel.elf.txt
$DMP -t kernel.elf > kernel.elf.symtab

$PARSERPATH RISCV64 kernel.c
$PARSERPATH RISCV64 --mmbytes kernel.c > kernel.sigs
cp ./kernel.* kernel/

echo $(pwd)

PATH=$HOL4_ROOT/bin:$PATH which Holmake
PATH=$HOL4_ROOT/bin:$PATH $DECOMP --fast $(pwd)/kernel
cp kernel_mc_graph.txt ASMFuns.txt

export L4V_ARCH=RISCV64
export TV_ROOT=/home/yshen/work/verificatin
./graphlang-export.sh kernel.c ./CFuns.txt

