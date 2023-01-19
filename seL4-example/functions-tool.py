#!/usr/bin/env python3

# Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
# Copyright 2023, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Perform various minor fixups and analyses on the outputs of l4v
# and decompilation, before passing them as inputs to graph-refine:
# - Generate StackBounds.txt using a simplified stack usage analysis
#   (see below).
# - Generate functions-list.txt containing the list of function names
#   that are common to CFunctions.txt and ASMFunctions.txt.
# - RISCV64 ASMFunctions.txt fixups:
#   - Fix the values loaded by AUIPC instructions, since the decompiler
#     currently truncates these to 32 bits.
#   - Rename `sfence_vma` to `sfence.vma`.

import argparse
import os
import re
import sys

from pathlib import Path
from typing import (Callable, Iterable, Iterator, Mapping, NamedTuple,
                    Optional, Sequence, Set, TextIO, Tuple, TypeVar, Union, Protocol)


K = TypeVar('K')
V = TypeVar('V')
R = TypeVar('R')
T = TypeVar('T')
L = TypeVar('L')

Elim = Callable[[T], R]


# Exceptions that may occur during parsing.

class UnexpectedEofError(Exception):
    pass


class BadFileFormatError(Exception):
    pass


class UnexpectedInput(Exception):
    pass


class DuplicateNode(Exception):
    pass


class DuplicateFunction(Exception):
    pass


class MalformedFunction(Exception):
    pass


class MalformedInstruction(Exception):
    pass


# A simple parser for graph-lang files.

class GraphLangNode(Protocol):
    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        ...


class BasicNode(NamedTuple):
    succ: str
    assign: str

    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        return basic(self)


class CallNode(NamedTuple):
    succ: str
    callee: str
    args: str

    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        return call(self)


class CondNode(NamedTuple):
    succ_true: str
    succ_false: str
    expr: str

    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        return cond(self)


GraphLangNodes = Mapping[str, GraphLangNode]


class GraphLangFunction(NamedTuple):
    args: str
    nodes: GraphLangNodes
    entry: Optional[str]


GraphLang = Mapping[str, GraphLangFunction]


def parse_graph_lang(file_path: Path, structs: bool) -> GraphLang:
    functions: dict[str, GraphLangFunction] = {}

    cur_fn_name: Optional[str] = None
    cur_fn_args: Optional[str] = None
    cur_fn_nodes: dict[str, GraphLangNode] = {}
    cur_fn_entry: Optional[str] = None

    function_re = re.compile(r'Function (?P<name>\S+) (?P<args>\S.*)')
    basic_re = re.compile(r'(?P<label>\S+) Basic (?P<succ>\S+) (?P<assign>\S.*)')
    call_re = re.compile(r'(?P<label>\S+) Call (?P<succ>\S+) (?P<callee>\S+) (?P<args>\S.*)')
    cond_re = re.compile(
        r'(?P<label>\S+) Cond (?P<succ_true>\S+) (?P<succ_false>\S+) (?P<expr>\S.*)')
    entry_re = re.compile(r'EntryPoint (?P<entry>\w+)')
    struct_re = re.compile(r'Struct(?:Field)? ')

    def reset_cur_fn() -> None:
        nonlocal cur_fn_name, cur_fn_nodes, cur_fn_entry
        cur_fn_name = None
        cur_fn_nodes = {}
        cur_fn_entry = None

    def add_cur_fn() -> None:
        try:
            if cur_fn_name is None:
                return
            if cur_fn_name in functions:
                raise DuplicateFunction(cur_fn_name)
            if cur_fn_nodes:
                if cur_fn_entry is None or cur_fn_entry not in cur_fn_nodes:
                    raise MalformedFunction(cur_fn_name)
            assert cur_fn_args is not None
            functions[cur_fn_name] = GraphLangFunction(nodes=cur_fn_nodes,
                                                       args=cur_fn_args,
                                                       entry=cur_fn_entry)
        finally:
            reset_cur_fn()

    with open(file_path) as input:

        for num, line in enumerate(input):
            line = line.strip()

            match = function_re.fullmatch(line)
            if match is not None:
                add_cur_fn()
                cur_fn_name = match['name']
                cur_fn_args = match['args']
                continue

            def unexpected():
                raise UnexpectedInput(num, line)

            def need_cur_fn():
                if cur_fn_name is None:
                    unexpected()

            def need_no_cur_fn():
                if cur_fn_name is not None:
                    unexpected()

            def add_node(label: str, node: GraphLangNode):
                need_cur_fn()
                if label in cur_fn_nodes:
                    raise DuplicateNode(cur_fn_name, label)
                cur_fn_nodes[label] = node

            match = basic_re.fullmatch(line)
            if match is not None:
                basic_node = BasicNode(succ=match['succ'],
                                       assign=match['assign'])
                add_node(match['label'], basic_node)
                continue

            match = call_re.fullmatch(line)
            if match is not None:
                call_node = CallNode(succ=match['succ'],
                                     callee=match['callee'],
                                     args=match['args'])
                add_node(match['label'], call_node)
                continue

            match = cond_re.fullmatch(line)
            if match is not None:
                cond_node = CondNode(succ_true=match['succ_true'],
                                     succ_false=match['succ_false'],
                                     expr=match['expr'])
                add_node(match['label'], cond_node)
                continue

            match = entry_re.fullmatch(line)
            if match is not None:
                need_cur_fn()
                cur_fn_entry = match['entry']
                continue

            if structs:
                match = struct_re.match(line)
                if match is not None:
                    need_no_cur_fn()
                    continue

            if line != '':
                unexpected()

        add_cur_fn()
        return functions


def emit_graph_lang(graph_lang: GraphLang) -> Iterator[str]:

    def emit_basic(node: BasicNode) -> str:
        return f'Basic {node.succ} {node.assign}'

    def emit_call(node: CallNode) -> str:
        return f'Call {node.succ} {node.callee} {node.args}'

    def emit_cond(node: CondNode) -> str:
        return f'Cond {node.succ_true} {node.succ_false} {node.expr}'

    def emit_node(label: str, node: GraphLangNode) -> str:
        node_str = node.elim(basic=emit_basic, call=emit_call, cond=emit_cond)
        return f'{label} {node_str}\n'

    def emit_function(name: str, function: GraphLangFunction) -> Iterator[str]:
        yield f'Function {name} {function.args}\n'

        for label, node in function.nodes.items():
            yield emit_node(label, node)

        if function.entry is not None:
            yield f'EntryPoint {function.entry}\n'

    prev_nodes: Optional[GraphLangNodes] = None

    for name, function in graph_lang.items():
        if prev_nodes is not None and function.nodes or prev_nodes:
            yield '\n'

        yield from emit_function(name, function)
        prev_nodes = function.nodes


# A simple parser for ELF dumps.
# Since we don't need to reproduce the dump, we only record the info we need.

class ElfNode(Protocol):
    def elim(self, instr: Elim['ElfInstr', R], data: Elim['ElfData', R]) -> R:
        ...


class ElfInstr(NamedTuple):
    binary: str
    opcode: str
    args: Optional[str]

    def elim(self, instr: Elim['ElfInstr', R], data: Elim['ElfData', R]) -> R:
        return instr(self)


class ElfData(NamedTuple):
    data: str

    def elim(self, instr: Elim['ElfInstr', R], data: Elim['ElfData', R]) -> R:
        return data(self)


ElfNodes = Mapping[str, ElfNode]


class ElfFunction(NamedTuple):
    section: Optional[str]
    nodes: ElfNodes


ElfFunctions = Mapping[str, ElfFunction]


def parse_elf_txt(file_path: Path) -> ElfFunctions:
    functions: dict[str, ElfFunction] = {}

    cur_section: Optional[str] = None
    cur_fn_name: Optional[str] = None
    cur_fn_nodes: dict[str, ElfNode] = {}

    elf_file_format_re = re.compile(r'.+:\s+file format elf(?:32|64)-(?:\w+)')
    elf_section_head_re = re.compile(r'Disassembly of section (?P<section>\S+):')
    elf_symbol_head_re = re.compile(r'(?P<addr>\w+) <(?P<name>\S+)>:')
    elf_instr_re = re.compile(
        r'(?P<addr>\w+):\t(?P<bin>\w+)\s+\t(?P<opcode>\S+)(?:\t(?P<args>.+))?')
    elf_data_re = re.compile(r'(?P<addr>\w+):\t(?P<data>[^\t]+)')

    def reset_cur_fn() -> None:
        nonlocal cur_fn_name, cur_fn_nodes
        cur_fn_name = None
        cur_fn_nodes = {}

    def add_cur_fn() -> None:
        try:
            if cur_fn_name is None:
                return
            if cur_fn_name in functions:
                raise DuplicateFunction(cur_fn_name)
            functions[cur_fn_name] = ElfFunction(section=cur_section,
                                                 nodes=cur_fn_nodes)
        finally:
            reset_cur_fn()

    def parse_file(lines: Iterable[Tuple[int, str]]) -> None:
        nonlocal cur_section, cur_fn_name

        lines = iter(lines)
        try:
            num, line = next(lines)
            match = elf_file_format_re.fullmatch(line)
            if not match:
                raise BadFileFormatError(num, line)
        except StopIteration:
            raise UnexpectedEofError

        for num, line in lines:
            match = elf_section_head_re.fullmatch(line)
            if match:
                cur_section = match['section']
                continue

            def unexpected():
                raise UnexpectedInput(num, line)

            def add_node(addr: str, node: ElfNode):
                if cur_fn_name is None:
                    unexpected()
                if addr in cur_fn_nodes:
                    raise DuplicateNode(cur_fn_name, addr)
                cur_fn_nodes[addr] = node

            match = elf_symbol_head_re.fullmatch(line)
            if match:
                add_cur_fn()
                cur_fn_name = match['name']
                continue

            match = elf_instr_re.fullmatch(line)
            if match:
                node = ElfInstr(binary=match['bin'],
                                opcode=match['opcode'],
                                args=match['args'])
                add_node(match['addr'], node)
                continue

            match = elf_data_re.fullmatch(line)
            if match:
                add_node(match['addr'], ElfData(data=match['data']))
                continue

            unexpected()

        add_cur_fn()

    def clean_lines(lines: Iterable[str]) -> Iterator[Tuple[int, str]]:
        stripped_lines = (line.strip() for line in lines)
        return ((num, line) for num, line in enumerate(stripped_lines) if line != '')

    with open(file_path) as input:
        parse_file(clean_lines(input))
        return functions


# Find the function names in common between two graph-lang specs.

def c_fn_name(name: str) -> str:
    assert name.startswith("Kernel_C.")
    name = name[len("Kernel_C."):]
    if name.startswith("StrictC'"):
        return name[len("StrictC'"):]
    return name


def common_functions(c: GraphLang, asm: GraphLang) -> Sequence[str]:
    # Skip empty C functions
    c_fn_names = {c_fn_name(name) for name, function in c.items() if function.nodes}
    return sorted(c_fn_names & asm.keys())


# Fixups for RISCV64 ASMFunctions.txt.

def fixup_sfence_vma(asm_functions: GraphLang) -> GraphLang:
    # The decompiler uses a name for sfence.vma that confuses graph-refine,
    # so we rename it.

    def fixup_name(name: str) -> str:
        return name.replace('sfence_vma', 'sfence.vma')

    def fixup_basic(node: BasicNode) -> GraphLangNode:
        return node

    def fixup_call(node: CallNode) -> GraphLangNode:
        return CallNode(succ=node.succ,
                        callee=fixup_name(node.callee),
                        args=node.args)

    def fixup_cond(node: CondNode) -> GraphLangNode:
        return node

    def fixup_node(node: GraphLangNode) -> GraphLangNode:
        return node.elim(basic=fixup_basic, call=fixup_call, cond=fixup_cond)

    def fixup_function(function: GraphLangFunction) -> GraphLangFunction:
        nodes = {label: fixup_node(node) for label, node in function.nodes.items()}
        return GraphLangFunction(args=function.args,
                                 nodes=nodes,
                                 entry=function.entry)

    return {fixup_name(name): fixup_function(function)
            for name, function in asm_functions.items()}


def fixup_auipc(asm_functions: GraphLang, elf_txt: ElfFunctions) -> GraphLang:
    # The RISCV64 decompiler truncates instruction addresses to 32 bits,
    # and this means that AUIPC instructions load incorrect values.

    class AUIPC(NamedTuple):
        address: int
        offset: int

    auipc_args_re = re.compile(r'(?:\w+),(?P<offset>0x[\dA-Fa-f]+)')
    auipc_expr_re = re.compile(r'1 (?P<reg>\w+) Word 64 Num (?P<val>\d+) Word 64')

    def get_auipcs(elf_nodes: ElfNodes) -> Mapping[int, AUIPC]:
        auipcs: dict[int, AUIPC] = {}

        def handle_data(data: ElfData) -> None:
            pass

        for address, node in elf_nodes.items():
            addr_int = int(address, 16)
            addr_int32 = addr_int % (1 << 32)

            def handle_instr(instr: ElfInstr) -> None:
                if instr.opcode == 'auipc':
                    assert instr.args is not None
                    match = auipc_args_re.fullmatch(instr.args)
                    if not match:
                        raise MalformedInstruction(address, instr)
                    offset = int(match['offset'], 16) << 12
                    auipcs[addr_int32] = AUIPC(address=addr_int, offset=offset)

            node.elim(instr=handle_instr, data=handle_data)

        return auipcs

    def fixup_function(name: str, function: GraphLangFunction) -> GraphLangFunction:
        if function.entry is None:
            return function

        auipcs = get_auipcs(elf_txt[name].nodes)

        def fixup_cond(node: CondNode) -> GraphLangNode:
            return node

        def fixup_call(node: CallNode) -> GraphLangNode:
            return node

        def fixup_node(label: str, node: GraphLangNode) -> GraphLangNode:

            def fixup_basic(node: BasicNode) -> GraphLangNode:
                addr_int32 = int(label, 16)
                auipc = auipcs.get(addr_int32)
                if auipc is None:
                    return node
                match = auipc_expr_re.fullmatch(node.assign)
                if not match:
                    raise MalformedInstruction(label, node)
                reg = match['reg']
                old_val = int(match['val'])
                assert old_val == (addr_int32 + auipc.offset) % (1 << 32)
                new_val = auipc.address + auipc.offset
                return BasicNode(succ=node.succ,
                                 assign=f'1 {reg} Word 64 Num {new_val} Word 64')

            return node.elim(basic=fixup_basic, call=fixup_call, cond=fixup_cond)

        nodes = {label: fixup_node(label, node) for label, node in function.nodes.items()}
        return GraphLangFunction(args=function.args,
                                 nodes=nodes,
                                 entry=function.entry)

    return {name: fixup_function(name, function)
            for name, function in asm_functions.items()}


def asm_fixups(arch: str, asm_functions: GraphLang, elf_txt: ElfFunctions) -> GraphLang:
    if arch == 'RISCV64':
        asm_functions = fixup_sfence_vma(asm_functions)
        asm_functions = fixup_auipc(asm_functions, elf_txt)
    return asm_functions


# Generate StackBounds.txt from ASMFunctions.txt and kernel.elf.txt.

# This is a temporary replacement for the StackBounds computation in
# graph-refine, since the latter currently has some unfixed bugs that
# are preventing it from producing results. This script requires a
# manual configuration of recursion limits, so is less automatic than
# the graph-refine StackBounds computation, but is currently more
# reliable.

# As in the original graph-refine StackBounds computation, we allow for
# a limited form of recursion which is controlled by a boolean function
# argument, such that functions may recurse at most once. We deal with
# this by constructing a non-recursive call graph from the original
# recursive call graph. Each functions which may recurse is split into
# two virtual nodes. Edges are then added and removed, such that the
# result is non-recursive. Unlike the original graph-refine StackBounds
# computation, which did this automatically, we require a hand-crafted
# specification of which nodes to split, and which edges to add and
# remove.

# Recursive functions must be controlled by a boolean argument, which
# should be used to differentiate between calls which may recurse and
# those which may not. Stack usage bounds are then given as conditional
# expressions in terms of that argument.

# To specify how to construct a non-recursive call graph, we first give
# a mapping from each function that may recurse to a GraphLang
# expression for the argument which controls recursion. The latter may
# be a register or a stack slot. Each specified function is split into a
# pair of nodes, with each node in the pair given as a tuple of the
# function name and one of the two possible values of the boolean
# controlling argument. In the resulting graph, each of the split nodes
# initially has the same edges as in the original graph.

# To make the graph non-recursive, we then give lists of edges to
# include and exclude from the modified graph. An edge is given as a
# pair of nodes. A node is given in one of two forms. For a function
# which does not recurse, the node is simply given as the name of the
# function. As noted above, each functions that may recurse has two
# nodes, each given as a pair of the function name and the value of the
# boolean variable at invocations corresponding to that node.

# Following are possible specifications for seL4. We
# have several different specifications, since different compilers,
# configurations and optimisation levels result in different functions
# being inlined. We try all configurations until we find one that
# results in an acyclic graph.

def sel4_recurse_spec_1(finalise_cap_rec: str, cte_delete_rec: str) -> 'RecurseSpec':
    return recurse_spec(
        # The two functions which may recurse.
        recurse={'finaliseCap': finalise_cap_rec,
                 'cteDelete': cte_delete_rec},
        # `cteDelete` may directly recurse to itself.
        # The recursive call takes 0 for the controlling argument.
        include=((('cteDelete', 1), ('cteDelete', 0)),),
        # `finaliseCap` may indirectly recurse via `suspend` or `deletingIRQHandler`, but
        # not if the controlling argument took the value 1. `cteDeleteOne` may call
        # `finaliseCap`, but only the copy that may not recurse.
        exclude=((('finaliseCap', 1), 'suspend'),
                 (('finaliseCap', 1), 'deletingIRQHandler'),
                 ('cteDeleteOne', ('finaliseCap', 0))))


def sel4_recurse_spec_2(finalise_cap_rec: str, cte_delete_rec: str) -> 'RecurseSpec':
    return recurse_spec(
        # The two functions which may recurse.
        recurse={'finaliseCap': finalise_cap_rec,
                 'cteDelete': cte_delete_rec},
        # `cteDelete` may directly recurse to itself.
        # The recursive call takes 0 for the controlling argument.
        include=((('cteDelete', 1), ('cteDelete', 0)),),
        # `finaliseCap` may indirectly recurse via `suspend` or
        # `invokeIRQHandler_ClearIRQHandler`, but not if the controlling argument took the
        # value 1. `cteDeleteOne` may call `finaliseCap`, but only the copy that may not
        # recurse. This specification is equivalent to the previous one, except that the
        # compiler has realised that `deletingIRQHandler` and
        # `invokeIRQHandler_ClearIRQHandler` are identical, and has substituted one for
        # the other.
        exclude=((('finaliseCap', 1), 'suspend'),
                 (('finaliseCap', 1), 'invokeIRQHandler_ClearIRQHandler'),
                 ('cteDeleteOne', ('finaliseCap', 0))))


def sel4_recurse_spec_3(finalise_cap_rec: str, finalise_slot_rec: str) -> 'RecurseSpec':
    return recurse_spec(
        # The two functions which may recurse.
        recurse={'finaliseCap': finalise_cap_rec,
                 'finaliseSlot': finalise_slot_rec},
        # `finaliseSlot` may directly recurse to itself.
        # The recursive call takes 0 for the controlling argument.
        include=((('finaliseSlot', 1), ('finaliseSlot', 0)),),
        # `finaliseCap` may indirectly recurse via `cteDeleteOne` or `cancelIPC`,
        # but not if the controlling argument took the value 1.
        # `cteDeleteOne` may call `finaliseCap`, but only the
        # copy that may not recurse.
        exclude=((('finaliseCap', 1), 'cteDeleteOne'),
                 (('finaliseCap', 1), 'cancelIPC'),
                 ('cteDeleteOne', ('finaliseCap', 0))))


def empty_spec() -> 'RecurseSpec':
    return recurse_spec(recurse={}, include=(), exclude=())


def mk_stack_access(offset: int, stack_pointer: str, bits: int) -> str:
    word = f'Word {bits}'
    sp = f'Var {stack_pointer} {word}'

    def stack_acc(addr: str) -> str:
        return f'Op MemAcc {word} 2 Var stack Mem {addr}'

    if offset:
        return stack_acc(f'Op Plus {word} 2 {sp} Num {offset} {word}')
    else:
        return stack_acc(sp)


def sel4_recurse_specs(arch: str) -> list['RecurseSpec']:
    empty = empty_spec()
    if arch == 'ARM':
        finalise_cap_rec = mk_stack_access(offset=0, stack_pointer='r13', bits=32)
        return [sel4_recurse_spec_1(finalise_cap_rec=finalise_cap_rec,
                                    cte_delete_rec='Var r1 Word 32'),
                sel4_recurse_spec_2(finalise_cap_rec=finalise_cap_rec,
                                    cte_delete_rec='Var r1 Word 32'),
                sel4_recurse_spec_3(finalise_cap_rec=finalise_cap_rec,
                                    finalise_slot_rec='Var r2 Word 32'),
                empty]
    if arch == 'RISCV64':
        return [sel4_recurse_spec_1(finalise_cap_rec='Var r14 Word 64',
                                    cte_delete_rec='Var r11 Word 64'),
                sel4_recurse_spec_2(finalise_cap_rec='Var r14 Word 64',
                                    cte_delete_rec='Var r11 Word 64'),
                sel4_recurse_spec_3(finalise_cap_rec='Var r14 Word 64',
                                    finalise_slot_rec='Var r12 Word 64'),
                empty]
    return [empty]


# We construct a call graph.
# For a function which does not recurse, the node is simply identified
# by the function name. A function which may recurse is given two nodes,
# each identified by a pair of the function name with one of the two
# possible values of the controlling argument.
Node = Union[str, Tuple[str, int]]
MapSet = Mapping[K, frozenset[V]]
Edge = Tuple[Node, Node]
Edges = MapSet[Node, Node]
Graph = MapSet[L, L]


class RecurseSpec(NamedTuple):
    recurse: Mapping[str, str]
    include: Edges
    exclude: Edges


def build_map_set(pairs: Iterable[Tuple[K, V]]) -> MapSet[K, V]:
    d: dict[K, Set[V]] = {}
    for k, v in pairs:
        s = d.setdefault(k, set())
        s.add(v)
    return {k: frozenset(s) for k, s in d.items()}


def recurse_spec(recurse: Mapping[str, str], include: Iterable[Edge],
                 exclude: Iterable[Edge]) -> RecurseSpec:
    return RecurseSpec(recurse=recurse,
                       include=build_map_set(include),
                       exclude=build_map_set(exclude))


ElfInstrUsage = Callable[[ElfInstr], int]
NodeUsage = Callable[[Node], int]

arm_instr_push_re = re.compile(r'{(?P<regs>\w+(?:,\s*\w+)*)}')
arm_instr_sub_sp_re = re.compile(r'sp,\s*sp,\s*#(?P<bytes>\d+)(?:\s+;.*)?')
riscv64_instr_usage_re = re.compile(r'sp,sp,-(?P<bytes>\d+)')


def arm_instr_usage(instr: ElfInstr) -> int:
    if instr.opcode == 'push':
        assert instr.args is not None
        match = arm_instr_push_re.match(instr.args)
        return len(match['regs'].split(',')) * 4 if match else 0
    if instr.opcode == 'sub':
        assert instr.args is not None
        match = arm_instr_sub_sp_re.fullmatch(instr.args)
        return int(match['bytes']) if match else 0
    return 0


def riscv64_instr_usage(instr: ElfInstr) -> int:
    if instr.opcode == 'addi':
        assert instr.args is not None
        match = riscv64_instr_usage_re.fullmatch(instr.args)
        if match:
            return int(match['bytes'])
    return 0


arch_instr_usage: Mapping[str, ElfInstrUsage] = {'ARM': arm_instr_usage,
                                                 'RISCV64': riscv64_instr_usage}


def elf_funs_stack_usage(funs: ElfFunctions, instr_usage: ElfInstrUsage) -> NodeUsage:

    def node_usage(node: ElfNode) -> int:
        return node.elim(instr_usage, lambda _: 0)

    def fun_usage(fun: ElfFunction) -> int:
        return sum(node_usage(node) for node in fun.nodes.values())

    function_usages: Mapping[str, int] = {name: fun_usage(fun) for name, fun in funs.items()}

    def get_usage(fun: Node) -> int:
        return function_usages.get(unsplit_label(fun), 0)

    return get_usage


def callees_of(asm_fun: GraphLangFunction) -> Iterator[str]:
    for node in asm_fun.nodes.values():
        if isinstance(node, CallNode):
            yield node.callee


def call_graph_of(asm_functions: GraphLang) -> Graph[str]:
    return {label: frozenset(callees_of(fun))
            for label, fun in asm_functions.items()}


def acyclic_graph_of(cyclic_graph: Graph[str], spec: RecurseSpec) -> Graph[Node]:
    def split_label(old_label: str) -> list[Node]:
        return [(old_label, 0), (old_label, 1)] if old_label in spec.recurse else [old_label]

    def split_labels(old_labels: frozenset[str]) -> frozenset[Node]:
        return frozenset(new_label
                         for old_label in old_labels
                         for new_label in split_label(old_label))

    def new_succs(old_label: str, new_label: Node):
        old_succs = cyclic_graph[old_label] - frozenset({old_label}) \
            if old_label in spec.recurse else cyclic_graph[old_label]
        include = spec.include.get(new_label, frozenset())
        exclude = spec.exclude.get(new_label, frozenset())
        return (split_labels(old_succs) | include) - exclude

    return {new_label: new_succs(old_label, new_label)
            for old_label in cyclic_graph
            for new_label in split_label(old_label)}


def unsplit_label(label: Node) -> str:
    return label if isinstance(label, str) else label[0]


# To sanity-check the construction of the acyclic graph, we can reduce it back to
# a cyclic graph, and compare the result to the original call graph.
# Currently, this check fails for seL4 on RISC-V, because the decompiler fails to
# recognise the recursive call in `cteDelete`, but we manually insert one into the
# acyclic graph via the RecurseSpec.
def cyclic_graph_of(acyclic_graph: Graph[Node]) -> Graph[str]:
    d: dict[str, Set[str]] = {}

    for label, succs in acyclic_graph.items():
        s = d.setdefault(unsplit_label(label), set())
        for succ in succs:
            s.add(unsplit_label(succ))

    return {k: frozenset(v) for k, v in d.items()}


def checked_acyclic_call_graph_of(cyclic_graph: Graph[str], spec: RecurseSpec) -> Graph[Node]:
    acyclic_graph: Graph[Node] = acyclic_graph_of(cyclic_graph, spec)
    assert cyclic_graph_of(acyclic_graph) == cyclic_graph
    return acyclic_graph


class CyclicGraph(Exception):
    pass


def acyclic_stack_usages(graph: Graph[Node], local_usage: NodeUsage) -> Mapping[Node, int]:
    global_usage: dict[Node, int] = {}

    # We check that the graph is acyclic as we go.
    ancestry: Set[Node] = set()

    def visit(node: Node):
        ancestry.add(node)
        callee_usage = 0
        for succ in graph[node]:
            if succ in ancestry:
                raise CyclicGraph(node, succ)
            if succ not in global_usage:
                visit(succ)
            callee_usage = max(callee_usage, global_usage[succ])
        global_usage[node] = local_usage(node) + callee_usage
        ancestry.remove(node)

    for n in graph.keys():
        visit(n)

    return global_usage


class StackUsage(Protocol):
    def elim(self, simple: Elim['SimpleStackUsage', R], split: Elim['SplitStackUsage', R]) -> R:
        ...


class SimpleStackUsage(NamedTuple):
    usage: int

    def elim(self, simple: Elim['SimpleStackUsage', R], split: Elim['SplitStackUsage', R]) -> R:
        return simple(self)


class SplitStackUsage(NamedTuple):
    control: str
    usage_0: int
    usage_1: int

    def elim(self, simple: Elim['SimpleStackUsage', R], split: Elim['SplitStackUsage', R]) -> R:
        return split(self)


class StackUsages(NamedTuple):
    spec: RecurseSpec
    usages: Mapping[str, StackUsage]


def cyclic_stack_usage(funs: Iterable[str],
                       spec: RecurseSpec,
                       node_usages: Mapping[Node, int]) -> StackUsages:
    def usage(fun: str) -> StackUsage:
        if fun in spec.recurse:
            return SplitStackUsage(control=spec.recurse[fun],
                                   usage_0=node_usages[(fun, 0)],
                                   usage_1=node_usages[(fun, 1)])
        else:
            return SimpleStackUsage(usage=node_usages[fun])

    usages = {fun: usage(fun) for fun in funs}
    return StackUsages(spec=spec, usages=usages)


def calculate_stack_usages(specs: Sequence[RecurseSpec],
                           asm_functions: GraphLang,
                           node_usage: NodeUsage) -> StackUsages:
    call_graph: Graph[str] = call_graph_of(asm_functions)
    for spec in specs:
        try:
            acyclic_graph = acyclic_graph_of(call_graph, spec)
            usage = acyclic_stack_usages(acyclic_graph, node_usage)
            return cyclic_stack_usage(call_graph.keys(), spec, usage)
        except CyclicGraph:
            pass
    # Modified graph was still cyclic, so find all cycles in the original graph.
    import networkx  # type: ignore
    nx_graph = networkx.DiGraph()
    nx_graph.add_nodes_from(call_graph.values())
    nx_graph.add_edges_from([(x, y) for x, ys in call_graph.items() for y in ys])
    cycles = list(networkx.simple_cycles(nx_graph))
    raise CyclicGraph(cycles)


def stack_usage_renderer(bits: int) -> Callable[[StackUsage], str]:
    def render_simple(simple_usage: SimpleStackUsage) -> str:
        return f'Num {simple_usage.usage} Word {bits}'

    def render_split(split_usage: SplitStackUsage) -> str:
        return (f'Op IfThenElse Word {bits} 3'
                + f' Op Equals Bool 2 {split_usage.control} Num 0 Word {bits}'
                + f' Num {split_usage.usage_0} Word {bits}'
                + f' Num {split_usage.usage_1} Word {bits}')

    def render(usage: StackUsage) -> str:
        return f'{usage.elim(render_simple, render_split)}\n'

    return render


def render_stack_usages(usages: Mapping[str, StackUsage],
                        render: Callable[[StackUsage], str]) -> Iterator[str]:
    return (f'StackBound {fun} {render(usage)}' for fun, usage in usages.items())


arch_bits = {'ARM': 32, 'RISCV64': 64}


def stack_usages(asm_functions: GraphLang, elf_txt: ElfFunctions,
                 arch: str) -> Iterator[str]:
    elf_usage = elf_funs_stack_usage(elf_txt, arch_instr_usage[arch])
    usages = calculate_stack_usages(sel4_recurse_specs(arch), asm_functions, elf_usage)
    return render_stack_usages(usages.usages,
                               stack_usage_renderer(bits=arch_bits[arch]))


# Main program

def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description='Generate StackBounds.txt')
    parser.add_argument('--arch', metavar='L4V_ARCH', choices=('ARM', 'RISCV64'),
                        default=os.environ.get('L4V_ARCH'),
                        help='Target architecture (ARM or RISCV64)')
    parser.add_argument('--target-dir', metavar='DIRECTORY', type=Path,
                        default='.', help='Directory containing graph-refine inputs')
    parser.add_argument('--asm-functions-in', metavar='FILE', type=Path,
                        default='kernel_mc_graph.txt', help='ASM GraphLang input file')
    parser.add_argument('--c-functions-in', metavar='FILE', type=Path,
                        default='CFunctions.txt', help='C GraphLang input file')
    parser.add_argument('--elf-txt-in', metavar='FILE', type=Path,
                        default='kernel.elf.txt', help='Disassembled ELF file')
    parser.add_argument('--fixups', action=argparse.BooleanOptionalAction,
                        default=True, help='Apply fixups to ASM GraphLang')
    parser.add_argument('--asm-functions-out', metavar='FILE', type=Path,
                        help='ASM GraphLang output file')
    parser.add_argument('--stack-bounds-out', metavar='FILE', type=Path,
                        help='Stack bounds output file')
    parser.add_argument('--functions-list-out', metavar='FILE', type=Path,
                        help='Functions list output file')
    return parser.parse_args()


def main() -> None:
    args = parse_arguments()
    if args.arch is None:
        print('functions-tool: error: neither --arch nor L4V_ARCH was supplied',
              file=sys.stderr)
        exit(1)

    print('functions-tool: parsing input files', file=sys.stderr)
    asm_functions = parse_graph_lang(args.target_dir / args.asm_functions_in, structs=False)
    elf_txt = parse_elf_txt(args.target_dir / args.elf_txt_in)

    if args.fixups:
        print('functions-tool: applying fixups', file=sys.stderr)
        asm_functions = asm_fixups(args.arch, asm_functions, elf_txt)

    if args.functions_list_out is not None:
        print('functions-tool: generating functions-list.txt', file=sys.stderr)
        c_functions = parse_graph_lang(args.target_dir / args.c_functions_in, structs=True)
        with open(args.target_dir / args.functions_list_out, 'w') as fns_list_file:
            for fn in common_functions(c=c_functions, asm=asm_functions):
                fns_list_file.write(f'{fn}\n')

    if args.asm_functions_out is not None:
        print('functions-tool: generating ASMFunctions.txt', file=sys.stderr)
        with open(args.target_dir / args.asm_functions_out, 'w') as asm_fns_file:
            for line in emit_graph_lang(asm_functions):
                asm_fns_file.write(line)

    if args.stack_bounds_out is not None:
        print('functions-tool: generating StackBounds.txt', file=sys.stderr)
        with open(args.target_dir / args.stack_bounds_out, 'w') as stack_bounds_file:
            for line in stack_usages(asm_functions, elf_txt, args.arch):
                stack_bounds_file.write(line)


if __name__ == '__main__':
    main()
