#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# Makefile for building, decompiling & validating seL4.

# n.b. doesn't track the dependencies of the custom tools
# (e.g. standalone c-parser and decompiler) properly, so may not know to
# rebuild if a custom tool is updated.

# branch specific part (riscv branch)
L4V_ARCH?=RISCV64
L4V_FEATURES?=MCS

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

L4V_CONFIG := ${L4V_ARCH}$(if ${L4V_FEATURES},-${L4V_FEATURES},)
TARGET_NAME := ${L4V_CONFIG}${CONFIG_OPTIMISATION_LEVEL}
TARGET_DIR := target/${TARGET_NAME}

# We build our own kernel locally, so we can store builds
# according to their optimisation levels.
KERNEL_BUILD_ROOT := ${TARGET_DIR}/build
KERNEL_CMAKE_EXTRA_OPTIONS := -DKernelOptimisation=${CONFIG_OPTIMISATION_LEVEL}
include ${GREF_ROOT}/../l4v/spec/cspec/c/kernel.mk

# However, CFunctions.txt depends on l4v's kernel build.
# FIXME: the l4v build directory should really depend on L4V_FEATURES.
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

${TARGET_DIR}/summary.txt: ${TARGET_DIR}/kernel_all.c_pp
	echo Summary > pre_summary.txt
	bash mk_summ ${SOURCE_ROOT} >> pre_summary.txt
	bash mk_summ ${L4V_REPO_PATH} >> pre_summary.txt
	bash mk_summ ${HOL4_ROOT} >> pre_summary.txt
	bash mk_summ . >> pre_summary.txt
	mv pre_summary.txt summary.txt

KERNEL_FILES := kernel.elf.rodata kernel.elf.txt kernel.elf.symtab kernel_all.c_pp kernel.sigs kernel.elf
TARGET_FILES := target.py CFunctions.txt ASMFunctions.txt

KERNEL_PATHS := $(patsubst %, $(TARGET_DIR)/%, $(KERNEL_FILES))
TARGET_PATHS := $(patsubst %, $(TARGET_DIR)/%, $(TARGET_FILES))

KERNEL_TGZ := ${TARGET_DIR}/kernel.tar.gz
TARGET_TGZ := ${TARGET_DIR}/target.tar.gz

${KERNEL_TGZ}: ${KERNEL_PATHS}
	tar -czf $@ -C ${TARGET_DIR} ${KERNEL_FILES}

${TARGET_TGZ}: ${KERNEL_PATHS} ${TARGET_PATHS}
	tar -czf $@ -C ${TARGET_DIR} ${KERNEL_FILES} ${TARGET_FILES}

tar: ${KERNEL_TGZ} ${TARGET_TGZ}

${KERNEL_PATHS}: ${TARGET_DIR}/%: ${KERNEL_BUILD_ROOT}/%
	@mkdir -p ${TARGET_DIR}
	cp $< $@

#clean:
#	rm -rf build kernel.elf.* kernel_all* kernel.tar*

.PHONY: tar # clean

H4PATH := $(realpath ${HOL4_ROOT}/bin):${PATH}

IGNORES_ARM := restore_user_context,c_handle_fastpath_call,c_handle_fastpath_reply_recv
IGNORES_RISCV64 := # TODO

KERNEL_ALL_PP_FILES := ${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp ${KERNEL_BUILD_ROOT}/kernel_all.c_pp

# FIXME: This should be a prerequisite of some other essential target,
#        but for convenience during development, it is currently not.
${TARGET_DIR}/.diff: ${KERNEL_ALL_PP_FILES}
	diff -q --ignore-matching-lines='^#' ${KERNEL_ALL_PP_FILES}
	@mkdir -p ${TARGET_DIR}
	@touch $@

diff: ${TARGET_DIR}/.diff
.PHONY: diff

${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp: ${KERNEL_DEPS} ${CONFIG_DOMAIN_SCHEDULE}
	MAKEFILES= make -C ${CSPEC_DIR}/c ${L4V_KERNEL_BUILD_DIR}/kernel_all.c_pp

# the straight decompiler output, without post-processing
${TARGET_DIR}/ASMFunctions.raw: ${TARGET_DIR}/kernel.elf.txt ${TARGET_DIR}/kernel.sigs
	cd ${TARGET_DIR} && PATH=${H4PATH} ${DECOMP_SCRIPT} --fast ./kernel --ignore=${IGNORES_${L4V_CONFIG}}
	mv ${TARGET_DIR}/kernel_mc_graph.txt $@

${TARGET_DIR}/ASMFunctions.txt: ${TARGET_DIR}/ASMFunctions.raw ${TARGET_DIR}/kernel.elf.txt
	# AUIPC fixup
	python2 ${GREF_ROOT}/tools/check_addr.py ${TARGET_DIR}/ASMFunctions.raw ${TARGET_DIR}/kernel.elf.txt $@
	# sfence_vma fix-up
	sed -i 's/sfence_vma/sfence.vma/g' $@

${TARGET_DIR}/CFunctions.txt: ${L4V_KERNEL_BUILD_PATH}/kernel_all.c_pp ${L4V_REPO_PATH}/tools/asmrefine/*.thy
	@mkdir -p ${TARGET_DIR}
	MAKEFILES= make -C ${L4V_REPO_PATH}/proof/ SimplExport
	# FIXME: the following path should really depend on L4V_FEATURES.
	cp ${L4V_REPO_PATH}/proof/asmrefine/export/${L4V_ARCH}/CFunDump.txt $@

${TARGET_DIR}/target.py: target.py
	@mkdir -p ${TARGET_DIR}
	cp target.py $@

GRAPH_REFINE_INPUTS := \
  ${TARGET_DIR}/kernel.elf.rodata \
  ${TARGET_DIR}/kernel.elf.symtab \
  ${TARGET_DIR}/ASMFunctions.txt \
  ${TARGET_DIR}/CFunctions.txt \
  ${TARGET_DIR}/target.py \
  ${GREF_ROOT}/*.py

GRAPH_REFINE := python2 ${GREF_ROOT}/graph-refine.py

${TARGET_DIR}/StackBounds.txt: ${GRAPH_REFINE_INPUTS}
	# FIXME: this script is arch-specific (RISCV64)
	python3 ${GREF_ROOT}/tools/stack_bounds.py --asm-functions ${TARGET_DIR}/ASMFunctions.txt --elf-txt ${TARGET_DIR}/kernel.elf.txt > $@

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

GTG := ${GREF_ROOT}/graph-to-graph/
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
