#!/bin/bash
cwd=$(pwd)
cd ../quoll
./quoll -i $cwd/kernel.objdump -b handleSyscall -o $cwd/kernel.imm
cd $cwd
../chronos4.2/est kernel.imm
cplex < kernel.imm.ilp

