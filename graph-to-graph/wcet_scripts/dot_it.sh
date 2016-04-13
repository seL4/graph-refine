#!/bin/bash
set -e
python reconstruct.py --dot new-gcc-O2.imm.sol new-gcc-O2.imm.map new-gcc-O2/kernel.elf > worst.dot
dot -Tsvg worst.dot -o worst.svg
