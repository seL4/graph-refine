# Copyright 2019, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)

# Makefile for building, decompiling & validating seL4.

# n.b. doesn't track the dependencies of the custom tools
# (e.g. standalone c-parser and decompiler) properly, so may not know to
# rebuild if a custom tool is updated.

ifndef CONFIG_OPTIMISATION_LEVEL
  CONFIG_OPTIMISATION_LEVEL := -O1
endif

# FIXME: solver self-test is currently broken
SKIP_SOLV_TEST := SKIP

ifndef GREF_ROOT
  GREF_ROOT := $(realpath $(dir $(lastword ${MAKEFILE_LIST}))..)
endif

ifndef HOL4_ROOT
  HOL4_ROOT := $(realpath ${GREF_ROOT}/../HOL4)
endif

TARGET_NAME := ${L4V_ARCH}${CONFIG_OPTIMISATION_LEVEL}

# We build our own kernel locally, so we can store builds
# according to their optimisation levels.
KERNEL_BUILD_ROOT := target/${TARGET_NAME}
KERNEL_CMAKE_EXTRA_OPTIONS := -DKernelOptimisation=${CONFIG_OPTIMISATION_LEVEL}
include ${GREF_ROOT}/../l4v/spec/cspec/c/kernel.mk

# CFunctions.txt depends on l4v's kernel build.
L4V_KERNEL_BUILD_DIR := build/${L4V_ARCH}
L4V_KERNEL_BUILD_PATH := ${CSPEC_DIR}/c/${L4V_KERNEL_BUILD_DIR}

DECOMP_DIR := ${HOL4_ROOT}/examples/machine-code/graph
DECOMP_SCRIPT := $(shell PATH="${DECOMP_DIR}:${PATH}" sh -c "which decompile.py")

# sanity test configuration

$(if ${DECOMP_SCRIPT},,$(error decompile.py not executable in ${DECOMP_DIR}))

$(if $(wildcard ${HOL4_ROOT}/bin/Holmake ${HOL4_ROOT}/bin/build),, \
  $(error Holmake/build not found in ${HOL4_ROOT}/bin - first configure HOL4. \
  See INSTALL in HOL4, but skip the bin/build step))

SOLV=python ${GREF_ROOT}/solver.py

SOLV_TEST_SUCC := 'Solver self-test succ'
SOLV_TEST := $(shell $(if ${SKIP_SOLV_TEST}, echo ${SOLV_TEST_SUCC}, \
    ${SOLV} testq) | grep ${SOLV_TEST_SUCC})
$(if ${SOLV_TEST},,$(error Solver self-test failed (${SOLV} test)))

# compile and decompile

${KERNEL_BUILD_ROOT}/summary.txt: ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	echo Summary > pre_summary.txt
	bash mk_summ ${SOURCE_ROOT} >> pre_summary.txt
	bash mk_summ ${L4V_REPO_PATH} >> pre_summary.txt
	bash mk_summ ${HOL4_ROOT} >> pre_summary.txt
	bash mk_summ . >> pre_summary.txt
	mv pre_summary.txt summary.txt

KERNEL_FILES := kernel.elf.rodata kernel.elf.txt kernel.elf.symtab kernel_all.c_pp kernel.sigs kernel.elf
TARGET_FILES := target.py CFunctions.txt ASMFunctions.txt

KERNEL_PATHS := $(patsubst %, $(KERNEL_BUILD_ROOT)/%, $(KERNEL_FILES))
TARGET_PATHS := $(patsubst %, $(KERNEL_BUILD_ROOT)/%, $(TARGET_FILES))

KERNEL_TGZ := ${KERNEL_BUILD_ROOT}/kernel.tar.gz
TARGET_TGZ := ${KERNEL_BUILD_ROOT}/target.tar.gz

${KERNEL_TGZ}: ${KERNEL_PATHS}
	tar -czf $@ -C ${KERNEL_BUILD_ROOT} ${KERNEL_FILES}

${TARGET_TGZ}: ${KERNEL_PATHS} ${TARGET_PATHS}
	tar -czf $@ -C ${KERNEL_BUILD_ROOT} ${KERNEL_FILES} ${TARGET_FILES}

tar: ${KERNEL_TGZ} ${TARGET_TGZ}

clean:
	rm -rf build kernel.elf.* kernel_all* kernel.tar*

.PHONY: clean tar

H4PATH := $(realpath ${HOL4_ROOT}/bin):${PATH}

IGNORES := fastpath_restore,slowpath,fastpath_call,fastpath_reply_recv,restore_user_context,lockTLBEntry,lockTLBEntryCritical

${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp: ${KERNEL_DEPS} ${CONFIG_DOMAIN_SCHEDULE}
	MAKEFILES= make -C ${CSPEC_DIR}/c ${L4V_KERNEL_BUILD_DIR}/kernel_all.c_pp

${KERNEL_BUILD_ROOT}/ASMFunctions.txt: ${KERNEL_BUILD_ROOT}/kernel.elf.txt ${KERNEL_BUILD_ROOT}/kernel.sigs
	cd ${KERNEL_BUILD_ROOT} && PATH=${H4PATH} ${DECOMP_SCRIPT} --fast ./kernel --ignore=${IGNORES}
	mv ${KERNEL_BUILD_ROOT}/kernel_mc_graph.txt ${KERNEL_BUILD_ROOT}/ASMFunctions.txt

${KERNEL_BUILD_ROOT}/CFunctions.txt: ${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp ${L4V_REPO_PATH}/tools/asmrefine/*.thy
	MAKEFILES= make -C ${L4V_REPO_PATH}/proof/ SimplExportOnly
	cp ${L4V_REPO_PATH}/proof/asmrefine/${L4V_ARCH}/CFunDump.txt $@

${KERNEL_BUILD_ROOT}/target.py: ${KERNEL_BUILD_ROOT}/.cmake_done
	cp target.py $@

GRAPH_REFINE_INPUTS := \
  ${KERNEL_BUILD_ROOT}/kernel.elf.rodata \
  ${KERNEL_BUILD_ROOT}/kernel.elf.symtab \
  ${KERNEL_BUILD_ROOT}/ASMFunctions.txt \
  ${KERNEL_BUILD_ROOT}/CFunctions.txt \
  ${KERNEL_BUILD_ROOT}/target.py \
  ${GREF_ROOT}/*.py

GRAPH_REFINE := python ${GREF_ROOT}/graph-refine.py

${KERNEL_BUILD_ROOT}/StackBounds.txt: ${GRAPH_REFINE_INPUTS}
	${GRAPH_REFINE} ${KERNEL_BUILD_ROOT}

${KERNEL_BUILD_ROOT}/demo-report.txt: ${KERNEL_BUILD_ROOT}/StackBounds.txt ${GRAPH_REFINE_INPUTS}
	${GRAPH_REFINE} ${KERNEL_BUILD_ROOT} trace-to:$@.partial deps:Kernel_C.cancelAllIPC
	mv $@.partial $@

${KERNEL_BUILD_ROOT}/report.txt: ${KERNEL_BUILD_ROOT}/StackBounds.txt ${GRAPH_REFINE_INPUTS}
	${GRAPH_REFINE} ${KERNEL_BUILD_ROOT} trace-to:$@.partial all
	mv $@.partial $@

default: ${KERNEL_BUILD_ROOT}/report.txt

.PHONY: .FORCE
.FORCE:

# WCET (worst-case execution time) targets

GTG := ${GREF_ROOT}/graph-to-graph/
KERNEL_BUILD_ROOT_ABS := $(realpath KERNEL_BUILD_ROOT)

${KERNEL_BUILD_ROOT}/loop_counts_1.py: ${KERNEL_BUILD_ROOT}/StackBounds.txt ${GRAPH_REFINE_INPUTS}
	cd ${GTG} && python graph_to_graph.py ${KERNEL_BUILD_ROOT_ABS} handleSyscall --l
	cp ${KERNEL_BUILD_ROOT}/loop_counts.py $@

${KERNEL_BUILD_ROOT}/lb_reports/report_%.txt: ${KERNEL_BUILD_ROOT}/loop_counts_1.py
	mkdir -p ${KERNEL_BUILD_ROOT}/lb_reports
	cd ${GTG} && python convert_loop_bounds.py --worker-id $* ${KERNEL_BUILD_ROOT_ABS} &> ${KERNEL_BUILD_ROOT_ABS}/lb_reports/pre-report_$*.txt
	tail -n 500 ${KERNEL_BUILD_ROOT}/lb_reports/pre-report_$*.txt > $@
	rm ${KERNEL_BUILD_ROOT}/lb_reports/pre-report_$*.txt

ALL_LB_REPORTS := $(patsubst %, ${KERNEL_BUILD_ROOT}/lb_reports/report_%.txt, 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )

${KERNEL_BUILD_ROOT}/lb_reports/fin_report.txt: ${ALL_LB_REPORTS}
	cd ${GTG} && python convert_loop_bounds.py $* ${KERNEL_BUILD_ROOT_ABS} &> ${KERNEL_BUILD_ROOT_ABS}/lb_reports/pre-freport.txt
	mv ${KERNEL_BUILD_ROOT}/lb_reports/pre-freport.txt $@

lb: ${KERNEL_BUILD_ROOT}/lb_reports/fin_report.txt
