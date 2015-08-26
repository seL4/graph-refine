# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

# makefile for cross-compiling seL4 here, decompiling it,
# and doing a graph-refine test.

# n.b. this makefile doesn't track the dependencies of the custom tools
# (e.g. standalone c-parser and decompiler) properly, so may not know to
# rebuild if a custom tool is updated.

# necessary configuration
TOOLPREFIX?=../../toolchains-x86_64/arm-2010.09/bin/arm-none-eabi-
CC?=gcc
OBJDUMP?=${TOOLPREFIX}objdump

SOURCE_ROOT?=../../seL4
L4V_ROOT?=../../l4v
PARSERPATH?=${L4V_ROOT}/tools/c-parser/standalone-parser

DECOMP_DIR?=../../decompiler/graph

# standard configuration
UMM_TYPES=umm_types.txt
ARCH=arm
ARMV=armv6
PLAT=imx31
CPU=arm1136jf-s
FASTPATH=yes

# optional configuration

CONFIG_OPTIMISATION_O1=y

# sanity test configuration

OBJDUMP_PATH = $(shell which ${OBJDUMP})
$(if ${OBJDUMP_PATH},,$(error objdump ${OBJDUMP} not executable))

DECOMP_SCRIPT= $(shell PATH="${DECOMP_DIR}:${PATH}" sh -c "which decompile.py")
$(if ${DECOMP_SCRIPT},,$(error decompile.py not executable in ${DECOMP_DIR}))

HOLMAKE= $(shell which Holmake)
$(if ${HOLMAKE},,$(error Holmake not found - first install/configure HOL4))

SOLV_TEST = $(shell python ../solver.py testq | grep 'Solver self-test succ')
$(if ${SOLV_TEST},,$(error Solver self-test failed (python ../solver.py test)))


# compile and decompile

include ${SOURCE_ROOT}/Makefile

kernel.elf.rodata: kernel.elf
	${OBJDUMP} -z -D -j .rodata $^ > $@

kernel.elf.txt: kernel.elf
	${OBJDUMP} -d $^ > $@

kernel.elf.symtab: kernel.elf
	${OBJDUMP} -t $^ > $@

kernel.sigs: kernel_all.c_pp
	MAKEFILES= make -C ${PARSERPATH} standalone-cparser
	${PARSERPATH}/c-parser --mmbytes $^ > $@

kernel.tar.gz: kernel.elf.rodata kernel.elf.txt kernel.elf.symtab \
		kernel_all.c_pp kernel.sigs \
		kernel.elf
	tar -cvzf $@ $^

tar: kernel.tar.gz

ASMFunctions.txt: kernel.elf.txt kernel.sigs
	${DECOMP_SCRIPT} ./kernel --ignore=fastpath_restore,slowpath
	# we move the output to a new location to get around a problem where
	# the decompiler can fail leaving an incomplete output file.
	mv kernel_mc_graph.txt ASMFunctions.txt

CFunctions.txt: kernel_all.c_pp ../../l4v/tools/asmrefine/*.thy
	MAKEFILES= make -C ../../l4v/proof/ SimplExportOnly
	cp ../../l4v/proof/asmrefine/CFunDump.txt CFunctions.txt

GRAPH_REFINE_INPUTS= kernel.elf.rodata kernel.elf.symtab ASMFunctions.txt \
                CFunctions.txt target.py ../*.py

StackBounds.txt: ${GRAPH_REFINE_INPUTS}
	python ../graph-refine.py .

report.txt: StackBounds.txt ${GRAPH_REFINE_INPUTS}
	python ../graph-refine.py . report-to:partial-$@ all
	mv partial-$@ $@

default: report.txt

