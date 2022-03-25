#!/usr/bin/env python3

# Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
# Copyright 2022, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Generate StackBounds.txt from ASMFunctions.txt and kernel.elf.txt.

# This is a temporary replacement for the StackBounds computation in
# graph-refine, since the latter currently has some unfixed bugs that
# are preventing it from producing results. This script requires a
# manual configuration of recursion limits, so is less automatic than
# the graph-refine StackBounds computation, but is currently more
# reliable.

# For usage information, run:
#   stack_bounds.py --help

# Requires Python 3.8 (for Protocol typing)

import os
import re
import sys

from argparse import ArgumentParser, FileType
from typing import (Callable, Dict, FrozenSet, Iterable, Iterator, Mapping, NamedTuple,
                    Optional, Sequence, Set, TextIO, Tuple, TypeVar, Union, List, Protocol)


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

# Following are the specifications for seL4, compiled with GCC 10.3. We
# have several different specifications, since different compilers,
# configurations and optimisation levels result in different functions
# being inlined. We try all configurations until we find one that
# results in an acyclic graph.

def sel4_recurse_spec_O1(finalise_cap_rec: str, cte_delete_rec: str) -> 'RecurseSpec':
    return recurse_spec(
        # The two functions which may recurse.
        recurse={'finaliseCap': finalise_cap_rec,
                 'cteDelete': cte_delete_rec},
        # `cteDelete` may directly recurse to itself.
        # The recursive call takes 0 for the controlling argument.
        include=((('cteDelete', 1), ('cteDelete', 0)),),
        # `finaliseCap` may indirectly recurse via `suspend` or
        # `deletingIRQHandler`, but not if the controlling argument took
        # the value 1. `cteDeleteOne` may call `finaliseCap`, but only the
        # copy that may not recurse.
        exclude=((('finaliseCap', 1), 'suspend'),
                 (('finaliseCap', 1), 'deletingIRQHandler'),
                 ('cteDeleteOne', ('finaliseCap', 0))))


def sel4_recurse_spec_O2(finalise_cap_rec: str, finalise_slot_rec: str) -> 'RecurseSpec':
    return recurse_spec(
        # The two functions which may recurse.
        recurse={'finaliseCap': finalise_cap_rec,
                 'finaliseSlot': finalise_slot_rec},
        # `finaliseSlot` may directly recurse to itself.
        # The recursive call takes 0 for the controlling argument.
        include=((('finaliseSlot', 1), ('finaliseSlot', 0)),),
        # `finaliseCap` may indirectly recurse via `cteDeleteOne` or `cancelIPC`,
        # but not if the controlling argument took the value 1.
        # `cteDeleteOne` may call `finaliseCap`, but only the # copy that may not recurse.
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


def sel4_recurse_specs(arch: str) -> List['RecurseSpec']:
    empty = empty_spec()
    if arch == 'ARM':
        finalise_cap_rec = mk_stack_access(offset=0, stack_pointer='r13', bits=32)
        return [sel4_recurse_spec_O1(finalise_cap_rec=finalise_cap_rec,
                                     cte_delete_rec='Var r1 Word 32'),
                sel4_recurse_spec_O2(finalise_cap_rec=finalise_cap_rec,
                                     finalise_slot_rec='Var r2 Word 32'),
                empty]
    if arch == 'RISCV64':
        return [sel4_recurse_spec_O1(finalise_cap_rec='Var r14 Word 64',
                                     cte_delete_rec='Var r11 Word 64'),
                sel4_recurse_spec_O2(finalise_cap_rec='Var r14 Word 64',
                                     finalise_slot_rec='Var r12 Word 64'),
                empty]
    return [empty]


def parse_arguments():
    parser = ArgumentParser(description='Generate StackBounds.txt')
    parser.add_argument('--asm-functions', metavar='FILE', type=FileType(),
                        default='ASMFunctions.txt', help='ASM GraphLang input file')
    parser.add_argument('--elf-txt', metavar='FILE', type=FileType(),
                        default='kernel.elf.txt', help='Disassembled ELF file')
    parser.add_argument('--arch', metavar='L4V_ARCH', choices=('ARM', 'RISCV64'),
                        default=os.environ.get('L4V_ARCH'),
                        help='Architecture (ARM or RISCV64)')
    return parser.parse_args()


K = TypeVar('K')
V = TypeVar('V')
R = TypeVar('R')
T = TypeVar('T')


class Map(Mapping[K, V]):

    def __init__(self, d: Dict[K, V]):
        def getitem(key: K) -> V:
            return d[key]

        def iterator() -> Iterator:
            return iter(d)

        def length() -> int:
            return len(d)

        self.getitem: Callable[[K], V] = getitem
        self.iterator: Callable[[], Iterator] = iterator
        self.length: Callable[[], int] = length

    def __getitem__(self, item):
        return self.getitem(item)

    def __iter__(self):
        return self.iterator()

    def __len__(self):
        return self.length()


def mapping(pairs: Iterable[Tuple[K, V]]) -> Map[K, V]:
    return Map({k: v for k, v in pairs})


# For a function which does not recurse, the node is simply identified
# by the function name. A function which may recurse is given two nodes,
# each identified by a pair of the function name with one of the two
# possible values of the controlling argument.
Node = Union[str, Tuple[str, int]]
MapSet = Map[K, FrozenSet[V]]
Edge = Tuple[Node, Node]
Edges = MapSet[Node, Node]


class RecurseSpec(NamedTuple):
    recurse: Map[str, str]
    include: Edges
    exclude: Edges


def build_map_set(pairs: Iterable[Tuple[K, V]]) -> MapSet[K, V]:
    d: Dict[K, Set[V]] = {}
    for k, v in pairs:
        s = d.setdefault(k, set())
        s.add(v)
    return Map({k: frozenset(s) for k, s in d.items()})


def recurse_spec(recurse: Dict[str, str], include: Iterable[Edge],
                 exclude: Iterable[Edge]) -> RecurseSpec:
    return RecurseSpec(recurse=Map(recurse),
                       include=build_map_set(include),
                       exclude=build_map_set(exclude))


Elim = Callable[[T], R]


# I hate this, but I can't find a more reasonable way to make an algebraic
# datatype out of `NamedTuple`s while keeping mypy happy.
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


ElfNodes = Map[str, ElfNode]


class ElfFunction(NamedTuple):
    nodes: ElfNodes = Map({})
    section: Optional[str] = None


ElfFunctions = Map[str, ElfFunction]

elf_file_format_re = re.compile(r'.+:\s+file format elf(?:32|64)-(?:\w+)')
elf_section_head_re = re.compile(r'Disassembly of section (?P<section>\S+):')
elf_symbol_head_re = re.compile(r'(?P<addr>\w+) <(?P<name>\S+)>:')
elf_instr_re = re.compile(r'(?P<addr>\w+):\t(?P<bin>\w+)\s+\t(?P<opcode>\S+)(?:\t(?P<args>.+))?')
elf_data_re = re.compile(r'(?P<addr>\w+):\t(?P<data>[^\t]+)')


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


def parse_elf_txt(elf_txt: TextIO) -> ElfFunctions:
    functions: Dict[str, ElfFunction] = {}

    class CurrentFunctionInfo:
        section: Optional[str]
        name: Optional[str]
        nodes: Dict[str, ElfNode]

        def __init__(self):
            self.section = None
            self.reset()

        def reset(self):
            self.name = None
            self.nodes = {}

    current_fn: CurrentFunctionInfo = CurrentFunctionInfo()

    def add_current_fn():
        try:
            if current_fn.name is None:
                return
            if current_fn.name in functions:
                raise DuplicateFunction(current_fn.name)
            functions[current_fn.name] = ElfFunction(section=current_fn.section,
                                                     nodes=Map(current_fn.nodes))
        finally:
            current_fn.reset()

    def parse_file(lines: Iterable[Tuple[int, str]]):
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
                current_fn.section = match['section']
                continue

            def unexpected():
                raise UnexpectedInput(num, line)

            def add_node(addr: str, node: ElfNode):
                if current_fn.name is None:
                    unexpected()
                if addr in current_fn.nodes:
                    raise DuplicateNode(current_fn.name, addr)
                current_fn.nodes[addr] = node

            match = elf_symbol_head_re.match(line)
            if match:
                add_current_fn()
                current_fn.name = match['name']
                continue

            match = elf_instr_re.fullmatch(line)
            if match:
                add_node(match['addr'],
                         ElfInstr(binary=match['bin'], opcode=match['opcode'], args=match['args']))
                continue
            match = elf_data_re.fullmatch(line)
            if match:
                add_node(match['addr'], ElfData(data=match['data']))
                continue

            unexpected()

        add_current_fn()

    def clean_lines(lines: Iterable[str]) -> Iterator[Tuple[int, str]]:
        stripped_lines = (line.strip() for line in lines)
        return ((num, line) for num, line in enumerate(stripped_lines) if line != '')

    try:
        parse_file(clean_lines(elf_txt))
        return Map(functions)
    finally:
        elf_txt.close()


ElfInstrUsage = Callable[[ElfInstr], int]
NodeUsage = Callable[[Node], int]

arm_instr_push_re = re.compile(r'{(?P<regs>\w+(?:,\s*\w+)*)}')
arm_instr_sub_sp_re = re.compile(r'sp,\s*sp,\s*#(?P<bytes>\d+)(?:\s+;.*)?')


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


riscv64_instr_usage_re = re.compile(r'sp,sp,-(?P<bytes>\d+)')


def riscv64_instr_usage(instr: ElfInstr) -> int:
    if instr.opcode == 'addi':
        assert instr.args is not None
        match = riscv64_instr_usage_re.fullmatch(instr.args)
        if match:
            return int(match['bytes'])
    return 0


arch_instr_usage: Map[str, ElfInstrUsage] = Map({'ARM': arm_instr_usage,
                                                 'RISCV64': riscv64_instr_usage})


def elf_funs_stack_usage(funs: ElfFunctions, instr_usage: ElfInstrUsage) -> NodeUsage:

    def node_usage(node: ElfNode) -> int:
        return node.elim(instr_usage, lambda _: 0)

    def fun_usage(fun: ElfFunction) -> int:
        return sum(node_usage(node) for node in fun.nodes.values())

    function_usages: Map[str, int] = Map({name: fun_usage(fun) for name, fun in funs.items()})

    def get_usage(fun: Node) -> int:
        return function_usages.get(unsplit_label(fun), 0)

    return get_usage


class AsmNode(Protocol):
    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        ...


class BasicNode(NamedTuple):
    succ: str

    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        return basic(self)


class CallNode(NamedTuple):
    callee: str
    succ: str

    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        return call(self)


class CondNode(NamedTuple):
    succ_true: str
    succ_false: str

    def elim(self, basic: Elim['BasicNode', R], call: Elim['CallNode', R],
             cond: Elim['CondNode', R]) -> R:
        return cond(self)


AsmNodes = Map[str, AsmNode]


class AsmFunction(NamedTuple):
    nodes: AsmNodes
    entry: Optional[str]


AsmFunctions = Map[str, AsmFunction]


class MalformedFunction(Exception):
    pass


function_re = re.compile(r'Function (?P<name>\S+)')
basic_re = re.compile(r'(?P<label>\S+) Basic (?P<succ>\S+)')
call_re = re.compile(r'(?P<label>\S+) Call (?P<succ>\S+) (?P<callee>\S+)')
cond_re = re.compile(r'(?P<label>\S+) Cond (?P<succ_true>\S+) (?P<succ_false>\S+)')
entry_re = re.compile(r'EntryPoint (?P<entry>\w+)')


def parse_asm_functions(asm_functions: TextIO) -> AsmFunctions:
    functions: Dict[str, AsmFunction] = {}

    class CurrentFunctionInfo:
        name: Optional[str]
        nodes: Dict[str, AsmNode]
        entry: Optional[str]

        def __init__(self):
            self.reset()

        def reset(self):
            self.name = None
            self.nodes = {}
            self.entry = None

    current_fn: CurrentFunctionInfo = CurrentFunctionInfo()

    def mk_asm_function() -> AsmFunction:
        return AsmFunction(nodes=Map(current_fn.nodes), entry=current_fn.entry)

    def add_current_fn():
        try:
            if current_fn.name is None:
                return
            if current_fn.name in functions:
                raise DuplicateFunction(current_fn.name)
            if current_fn.nodes and (current_fn.entry is None
                                     or current_fn.entry not in current_fn.nodes):
                raise MalformedFunction(current_fn.name)
            functions[current_fn.name] = mk_asm_function()
        finally:
            current_fn.reset()

    def parse_file():
        for num, line in enumerate(asm_functions):
            line = line.strip()

            match = function_re.match(line)
            if match is not None:
                add_current_fn()
                current_fn.name = match['name']
                continue

            def unexpected():
                raise UnexpectedInput(num, line)

            def need_current_fn():
                if current_fn.name is None:
                    unexpected()

            def add_node(label: str, node: AsmNode):
                need_current_fn()
                if label in current_fn.nodes:
                    raise DuplicateNode(current_fn.name, label)
                current_fn.nodes[label] = node

            match = basic_re.match(line)
            if match is not None:
                add_node(match['label'], BasicNode(succ=match['succ']))
                continue
            match = call_re.match(line)
            if match is not None:
                add_node(match['label'], CallNode(callee=match['callee'], succ=match['succ']))
                continue
            match = cond_re.match(line)
            if match is not None:
                add_node(match['label'],
                         CondNode(succ_true=match['succ_true'], succ_false=match['succ_false']))
                continue

            match = entry_re.fullmatch(line)
            if match is not None:
                need_current_fn()
                current_fn.entry = match['entry']
                continue

            if line != '':
                unexpected()

        add_current_fn()

    try:
        parse_file()
        return Map(functions)
    finally:
        asm_functions.close()


L = TypeVar('L')
Graph = MapSet[L, L]


def callees_of(asm_fun: AsmFunction) -> Iterator[str]:
    # mypy bug: the generator version of the following does not type-check
    # return (node.callee for node in asm_fun.nodes.values() if isinstance(node, CallNode))
    for node in asm_fun.nodes.values():
        if isinstance(node, CallNode):
            yield node.callee


def call_graph_of(asm_functions: AsmFunctions) -> Graph[str]:
    return Map({label: frozenset(callees_of(fun)) for label, fun in asm_functions.items()})


def acyclic_graph_of(cyclic_graph: Graph[str], spec: RecurseSpec) -> Graph[Node]:
    def split_label(old_label: str) -> List[Node]:
        return [(old_label, 0), (old_label, 1)] if old_label in spec.recurse else [old_label]

    def split_labels(old_labels: FrozenSet[str]) -> FrozenSet[Node]:
        return frozenset(new_label
                         for old_label in old_labels
                         for new_label in split_label(old_label))

    def new_succs(old_label: str, new_label: Node):
        old_succs = cyclic_graph[old_label] - frozenset({old_label}) \
            if old_label in spec.recurse else cyclic_graph[old_label]
        include = spec.include.get(new_label, frozenset())
        exclude = spec.exclude.get(new_label, frozenset())
        return (split_labels(old_succs) | include) - exclude

    return Map({new_label: new_succs(old_label, new_label)
                for old_label in cyclic_graph
                for new_label in split_label(old_label)})


def unsplit_label(label: Node) -> str:
    return label if isinstance(label, str) else label[0]


# To sanity-check the construction of the acyclic graph, we can reduce it back to
# a cyclic graph, and compare the result to the original call graph.
# Currently, this check fails for seL4 on RISC-V, because the decompiler fails to
# recognise the recursive call in `cteDelete`, but we manually insert one into the
# acyclic graph via the RecurseSpec.
def cyclic_graph_of(acyclic_graph: Graph[Node]) -> Graph[str]:
    d: Dict[str, Set[str]] = {}

    for label, succs in acyclic_graph.items():
        s = d.setdefault(unsplit_label(label), set())
        for succ in succs:
            s.add(unsplit_label(succ))

    return Map({k: frozenset(v) for k, v in d.items()})


def checked_acyclic_call_graph_of(cyclic_graph: Graph[str], spec: RecurseSpec) -> Graph[Node]:
    acyclic_graph: Graph[Node] = acyclic_graph_of(cyclic_graph, spec)
    assert cyclic_graph_of(acyclic_graph) == cyclic_graph
    return acyclic_graph


class CyclicGraph(Exception):
    pass


def acyclic_stack_usages(graph: Graph[Node], local_usage: NodeUsage) -> Map[Node, int]:
    global_usage: Dict[Node, int] = {}

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

    return Map(global_usage)


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
    usages: Map[str, StackUsage]


def cyclic_stack_usage(funs: Iterable[str],
                       spec: RecurseSpec,
                       node_usages: Map[Node, int]) -> StackUsages:
    def usage(fun: str) -> StackUsage:
        if fun in spec.recurse:
            return SplitStackUsage(control=spec.recurse[fun],
                                   usage_0=node_usages[(fun, 0)],
                                   usage_1=node_usages[(fun, 1)])
        else:
            return SimpleStackUsage(usage=node_usages[fun])

    usages = Map({fun: usage(fun) for fun in funs})
    return StackUsages(spec=spec, usages=usages)


def stack_usage(specs: Sequence[RecurseSpec], asm_functions: TextIO, node_usage: NodeUsage) -> StackUsages:
    call_graph: Graph[str] = call_graph_of(parse_asm_functions(asm_functions))
    for spec in specs:
        try:
            usage: Map[Node, int] = acyclic_stack_usages(
                acyclic_graph_of(call_graph, spec), node_usage)
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


def render_stack_usage(bits: int) -> Callable[[StackUsage], str]:
    def render_simple(simple_usage: SimpleStackUsage) -> str:
        return f'Num {simple_usage.usage} Word {bits}'

    def render_split(split_usage: SplitStackUsage) -> str:
        return (f'Op IfThenElse Word {bits} 3'
                + f' Op Equals Bool 2 {split_usage.control} Num 0 Word {bits}'
                + f' Num {split_usage.usage_0} Word {bits}'
                + f' Num {split_usage.usage_1} Word {bits}')

    def render(usage: StackUsage) -> str:
        return usage.elim(render_simple, render_split)

    return render


def render_stack_usages(usages: Map[str, StackUsage],
                        render: Callable[[StackUsage], str]) -> Iterator[str]:
    return (f'StackBound {fun} {render(usage)}' for fun, usage in usages.items())


def main(asm_functions: TextIO, elf_txt: TextIO, arch: str, bits: int):
    elf_usage = elf_funs_stack_usage(parse_elf_txt(elf_txt), arch_instr_usage[arch])
    usages = stack_usage(sel4_recurse_specs(arch), asm_functions, elf_usage)
    for usage_line in render_stack_usages(usages.usages, render_stack_usage(bits=bits)):
        print(usage_line)


arch_bits = {'ARM': 32, 'RISCV64': 64}


def script_main():
    args = parse_arguments()
    if args.arch is None:
        print('error: stack_bounds: neither --arch nor L4V_ARCH was supplied',
              file=sys.stderr)
        exit(1)
    main(asm_functions=args.asm_functions,
         elf_txt=args.elf_txt,
         arch=args.arch,
         bits=arch_bits[args.arch])


if __name__ == '__main__':
    script_main()
