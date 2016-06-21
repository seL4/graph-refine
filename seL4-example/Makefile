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
CSPEC_PATH?=${L4V_ROOT}/spec/cspec/c

HOL4_ROOT?=../../HOL4
DECOMP_DIR?=${HOL4_ROOT}/examples/machine-code/graph

# standard configuration
UMM_TYPES=umm_types.txt
ARCH=arm
ARMV=armv7-a
PLAT=imx6
CPU=cortex-a9
FASTPATH=yes
CONFIG_DOMAIN_SCHEDULE=${CSPEC_PATH}/config_arm.c

# optional configuration

CONFIG_OPTIMISATION_O1=y

# sanity test configuration

OBJDUMP_PATH = $(shell which ${OBJDUMP})
$(if ${OBJDUMP_PATH},,$(error objdump ${OBJDUMP} not executable))

DECOMP_SCRIPT= $(shell PATH="${DECOMP_DIR}:${PATH}" sh -c "which decompile.py")
$(if ${DECOMP_SCRIPT},,$(error decompile.py not executable in ${DECOMP_DIR}))

$(if $(wildcard ${HOL4_ROOT}/bin/Holmake ${HOL4_ROOT}/bin/build),, \
  $(error Holmake/build not found in ${HOL4_ROOT}/bin - first configure HOL4. \
  See INSTALL in HOL4, but skip the bin/build step))

SOLV_TEST = $(shell python ../solver.py testq | grep 'Solver self-test succ')
$(if ${SOLV_TEST},,$(error Solver self-test failed (python ../solver.py test)))


# compile and decompile

include ${SOURCE_ROOT}/Makefile

kernel.elf.rodata: kernel.elf
	${OBJDUMP} -z -D -j .rodata $^ > $@

kernel.elf.txt: kernel.elf
	${OBJDUMP} -dz $^ > $@

kernel.elf.symtab: kernel.elf
	${OBJDUMP} -t $^ > $@

kernel.sigs: kernel_all.c_pp
	MAKEFILES= make -C ${PARSERPATH} standalone-cparser
	${PARSERPATH}/c-parser --mmbytes $^ > $@

summary.txt: kernel_all.c_pp 
	echo Summary > pre_summary.txt
	bash mk_summ ${SOURCE_ROOT} >> pre_summary.txt
	bash mk_summ ${L4V_ROOT} >> pre_summary.txt
	bash mk_summ ${HOL4_ROOT} >> pre_summary.txt
	bash mk_summ . >> pre_summary.txt
	mv pre_summary.txt summary.txt

kernel.tar.gz: kernel.elf.rodata kernel.elf.txt kernel.elf.symtab \
		kernel_all.c_pp kernel.sigs \
		kernel.elf
	tar -cvzf $@ $^

tar: kernel.tar.gz

H4PATH=$(realpath ${HOL4_ROOT}/bin):${PATH}

ASMFunctions.txt: kernel.elf.txt kernel.sigs
	PATH=${H4PATH} build
	PATH=${H4PATH} ${DECOMP_SCRIPT} --fast ./kernel --ignore=fastpath_restore,slowpath
	# we move the output to a new location to get around a problem where
	# the decompiler can fail leaving an incomplete output file.
	mv kernel_mc_graph.txt ASMFunctions.txt

L4V_KERNEL_ALL= ${CSPEC_PATH}/kernel_all.c_pp

$(L4V_KERNEL_ALL): .FORCE
	MAKEFILES= make -C ${L4V_ROOT}/spec c-kernel

KERNEL_ALL_FILES= kernel_all.c_pp $(L4V_KERNEL_ALL)

CFunctions.txt: $(KERNEL_ALL_FILES) ${L4V_ROOT}/tools/asmrefine/*.thy
	# it's important that the parser and compiler see the same source
	diff -qs --ignore-matching-lines='^#' ${KERNEL_ALL_FILES}
	MAKEFILES= make -C ${L4V_ROOT}/proof/ SimplExportOnly
	cp ${L4V_ROOT}/proof/asmrefine/CFunDump.txt CFunctions.txt

GRAPH_REFINE_INPUTS= kernel.elf.rodata kernel.elf.symtab ASMFunctions.txt \
                CFunctions.txt target.py ../*.py

StackBounds.txt: ${GRAPH_REFINE_INPUTS}
	python ../graph-refine.py .

report.txt: StackBounds.txt ${GRAPH_REFINE_INPUTS}
	python ../graph-refine.py . trace-to:partial-$@ all
	mv partial-$@ $@

default: report.txt

.PHONY: .FORCE
.FORCE:
