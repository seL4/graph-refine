#!/bin/ksh

PF=arm-none-eabi-
CC="$PF""gcc"
DMP="$PF""objdump"
export L4V_ROOT=/home/yshen/work/verificatin/l4v
export L4V_ARCH=ARM
PARSERPATH="$L4V_ROOT"/tools/c-parser/standalone-parser/c-parser
HOL4_ROOT=/home/yshen/work/verificatin/HOL4
DECOMP_DIR="$HOL_ROOT""/examples/machine-code/graph"
DECOMP="$HOL4_ROOT"/examples/machine-code/graph/decompile.py


echo $PF
echo $CC
echo $DMP
rm kernel/*

mkdir -p kernel

$CC  --static -nostdlib -O0 kernel.c -o kernelO0.elf
$CC  --static -nostdlib  -O1 kernel.c -o kernelO1.elf
$CC  --static -nostdlib -O2 kernel.c -o kernelO2.elf
$DMP -D kernelO1.elf > kernel.elf.rodata
$DMP -dz kernelO1.elf > kernel.elf.txt
$DMP -dz kernelO0.elf > kernelO0.elf.txt
$DMP -dz kernelO1.elf > kernelO1.elf.txt
$DMP -dz kernelO2.elf > kernelO2.elf.txt
$DMP -t kernelO1.elf > kernel.elf.symtab
cp kernelO1.elf kernel.elf

$PARSERPATH ARM kernel.c
$PARSERPATH ARM --mmbytes kernel.c > kernel.sigs
cp ./kernel.* kernel/

echo $(pwd)

PATH=$HOL4_ROOT/bin:$PATH which Holmake
PATH=$HOL4_ROOT/bin:$PATH $DECOMP --fast $(pwd)/kernel
cp kernel_mc_graph.txt ASMFuns.txt

export L4V_ARCH=ARM
export TV_ROOT=/home/yshen/work/verificatin
./graphlang-export.sh kernel.c ./CFuns.txt

