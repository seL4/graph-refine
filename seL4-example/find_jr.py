#!/usr/bin/env python3

import re
from argparse import ArgumentParser, FileType
from typing import (Callable, Dict, FrozenSet, Iterable, Iterator, Mapping, NamedTuple,
                    Optional, Set, TextIO, Tuple, TypeVar, Union, List, Protocol)


K = TypeVar('K')
V = TypeVar('V')
T = TypeVar('T')
R = TypeVar('R')


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

elf_file_format_re = re.compile(r'.+:\s+file format elf64-littleriscv')
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


def instr_is_jr(instr: ElfInstr) -> bool:
    return instr.opcode == 'jr'


def node_is_jr(node: ElfNode) -> bool:
    return node.elim(instr_is_jr, lambda _: False)


def fun_has_jr(fun: ElfFunction) -> bool:
    return any(node_is_jr(node) for node in fun.nodes.values())


def funs_with_jr(funs: ElfFunctions) -> Iterable[str]:
    return (name for name, fun in funs.items() if fun_has_jr(fun))


def script_main():
    for fun in funs_with_jr(parse_elf_txt(open('kernel.elf.txt'))):
        print(fun)

if __name__ == '__main__':
    script_main()
