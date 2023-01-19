#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# Makefile for building, decompiling & validating seL4.

# n.b. doesn't track the dependencies of the custom tools
# (e.g. standalone c-parser and decompiler) properly, so may not know to
# rebuild if a custom tool is updated.

ifndef KERNEL_CONFIG_OPTIMISATION_LEVEL
  KERNEL_CONFIG_OPTIMISATION_LEVEL := -O1
endif

L4V_CONFIG := ${L4V_ARCH}$(if ${L4V_FEATURES},-${L4V_FEATURES},)
TARGET_NAME := ${L4V_CONFIG}${KERNEL_CONFIG_OPTIMISATION_LEVEL}

ifndef TARGET_DIR
  TARGET_DIR := target/${TARGET_NAME}
endif

ifndef GRAPH_REFINE_ROOT
  GRAPH_REFINE_ROOT := $(realpath $(dir $(lastword ${MAKEFILE_LIST}))..)
endif

ifndef DECOMPILER
  DECOMPILER := ${GRAPH_REFINE_ROOT}/decompiler/decompile
endif

ifndef L4V_KERNEL_MK
  L4V_KERNEL_MK := $(realpath ${GRAPH_REFINE_ROOT}/../l4v/spec/cspec/c/kernel.mk)
endif

ifndef KERNEL_BUILD_ROOT
  KERNEL_BUILD_ROOT=${GRAPH_REFINE_ROOT}/seL4-example/build/${TARGET_NAME}
endif

KERNEL_BUILD_EXPORT_DIR := ${TARGET_DIR}

# We build our own kernel locally, so we can store builds
# according to their optimisation levels.
# This depends on KERNEL_BUILD_ROOT and KERNEL_BUILD_EXPORT_DIR.
include ${L4V_KERNEL_MK}

# However, CFunctions.txt depends on l4v's kernel build.
L4V_KERNEL_BUILD_DIR := build/${L4V_ARCH}
L4V_KERNEL_BUILD_PATH := ${CSPEC_DIR}/c/${L4V_KERNEL_BUILD_DIR}

${DECOMPILER}:
	@echo "No decompiler found. Use setup-decompiler.py to install one." >&2
	@exit 1

# Compile and decompile

${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp: ${KERNEL_DEPS} ${CONFIG_DOMAIN_SCHEDULE}
	MAKEFILES= make -C ${CSPEC_DIR}/c ${L4V_KERNEL_BUILD_DIR}/kernel_all.c_pp

# A quick check that the two kernel builds produce the same C source
${TARGET_DIR}/.diff: ${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	diff -q --ignore-matching-lines='^#' $^
	@mkdir -p ${TARGET_DIR}
	@touch $@

diff: ${TARGET_DIR}/.diff
.PHONY: diff

ASM_FUNCTIONS_DEPS := ${TARGET_DIR}/kernel.elf.txt ${TARGET_DIR}/kernel.sigs ${DECOMPILER} ${AUIPC_FIXUP}
ASM_FUNCTIONS := ${TARGET_DIR}/ASMFunctions.txt
ASM_FUNCTIONS_OUT := ${ASM_FUNCTIONS} ${TARGET_DIR}/kernel_output.txt ${TARGET_DIR}/StackBounds.txt

IGNORE_ARM := _start,c_handle_fastpath_call,c_handle_fastpath_reply_recv,restore_user_context

${ASM_FUNCTIONS_OUT} &: ${ASM_FUNCTIONS_DEPS}
	${DECOMPILER} ${TARGET_DIR}/kernel --ignore=${IGNORE_${L4V_ARCH}}
	${GRAPH_REFINE_ROOT}/seL4-example/functions-tool.py \
	  --target-dir ${TARGET_DIR} \
	  --asm-functions-out ASMFunctions.txt \
	  --stack_bounds-out StackBounds.txt

C_FUNCITONS_DEPS := \
  ${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp \
  ${L4V_REPO_PATH}/tools/asmrefine/*.thy \
  ${L4V_REPO_PATH}/tools/asmrefine/${L4V_ARCH}/*.thy

${TARGET_DIR}/CFunctions.txt: ${C_FUNCTIONS_DEPS}
	@mkdir -p ${TARGET_DIR}
	MAKEFILES= make -C ${L4V_REPO_PATH}/proof/ SimplExport
	cp ${L4V_REPO_PATH}/proof/asmrefine/export/${L4V_ARCH}/CFunDump.txt $@

TARGET_PY := ${GRAPH_REFINE_ROOT}/seL4-example/target-${L4V_ARCH}.py
${TARGET_DIR}/target.py: ${TARGET_PY}
	@mkdir -p ${TARGET_DIR}
	cp ${TARGET_PY} $@

GRAPH_REFINE_INPUTS := \
  ${TARGET_DIR}/kernel.elf.rodata \
  ${TARGET_DIR}/kernel.elf.symtab \
  ${TARGET_DIR}/ASMFunctions.txt \
  ${TARGET_DIR}/CFunctions.txt \
  ${TARGET_DIR}/target.py \
  ${GRAPH_REFINE_ROOT}/*.py

GRAPH_REFINE := python2 ${GRAPH_REFINE_ROOT}/graph-refine.py

${TARGET_DIR}/demo-report.txt: ${TARGET_DIR}/StackBounds.txt ${GRAPH_REFINE_INPUTS}
	${GRAPH_REFINE} ${TARGET_DIR} trace-to:$@.partial deps:Kernel_C.cancelAllIPC
	mv $@.partial $@

${TARGET_DIR}/report.txt: ${TARGET_DIR}/StackBounds.txt ${GRAPH_REFINE_INPUTS}
	${GRAPH_REFINE} ${TARGET_DIR} trace-to:$@.partial all
	mv $@.partial $@

${TARGET_DIR}/coverage.txt: ${TARGET_DIR}/StackBounds.txt ${GRAPH_REFINE_INPUTS}
	${GRAPH_REFINE} ${TARGET_DIR} trace-to:$@.partial coverage
	mv $@.partial $@

report: ${TARGET_DIR}/report.txt
coverage: ${TARGET_DIR}/coverage.txt
StackBounds: ${TARGET_DIR}/StackBounds.txt

.PHONY: report coverage StackBounds

default: report

.PHONY: .FORCE
.FORCE:

# WCET (worst-case execution time) targets

GTG := ${GRAPH_REFINE_ROOT}/graph-to-graph/
TARGET_DIR_ABS := $(realpath TARGET_DIR)

${TARGET_DIR}/loop_counts_1.py: ${TARGET_DIR}/StackBounds.txt ${GRAPH_REFINE_INPUTS}
	cd ${GTG} && python graph_to_graph.py ${TARGET_DIR_ABS} handleSyscall --l
	cp ${TARGET_DIR}/loop_counts.py $@

${TARGET_DIR}/lb_reports/report_%.txt: ${TARGET_DIR}/loop_counts_1.py
	@mkdir -p ${TARGET_DIR}/lb_reports
	cd ${GTG} && python convert_loop_bounds.py --worker-id $* ${TARGET_DIR_ABS} &> ${TARGET_DIR_ABS}/lb_reports/pre-report_$*.txt
	tail -n 500 ${TARGET_DIR}/lb_reports/pre-report_$*.txt > $@
	rm ${TARGET_DIR}/lb_reports/pre-report_$*.txt

ALL_LB_REPORTS := $(patsubst %, ${TARGET_DIR}/lb_reports/report_%.txt, 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )

${TARGET_DIR}/lb_reports/fin_report.txt: ${ALL_LB_REPORTS}
	cd ${GTG} && python convert_loop_bounds.py $* ${TARGET_DIR_ABS} &> ${TARGET_DIR_ABS}/lb_reports/pre-freport.txt
	mv ${TARGET_DIR}/lb_reports/pre-freport.txt $@

lb: ${TARGET_DIR}/lb_reports/fin_report.txt
