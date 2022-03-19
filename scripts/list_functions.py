#!/usr/bin/env python3

# Copyright 2022, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Given a directory containing ASMFunction.txt and CFunctions.txt,
# generate a list of function names common to both. Assumes that
# CFunctions.txt uses the Kernel_C namespace from the seL4 proofs.

import re
import sys

from pathlib import Path
from typing import Iterable, Optional, Sequence, Set, TextIO


class UnexpectedInput(Exception):
    pass


class DuplicateNode(Exception):
    pass


class DuplicateFunction(Exception):
    pass


class MalformedFunction(Exception):
    pass


function_re = re.compile(r'Function (?P<name>\S+)')
basic_re = re.compile(r'(?P<label>\S+) Basic \S+')
call_re = re.compile(r'(?P<label>\S+) Call \S+ \S+')
cond_re = re.compile(r'(?P<label>\S+) Cond \S+ \S+')
entry_re = re.compile(r'EntryPoint (?P<entry>\w+)')
struct_re = re.compile(r'Struct(?:Field)? ')


def parse_functions(functions_file: Path, structs: bool) -> Iterable[str]:
    class CurrentFunctionInfo:
        name: Optional[str]
        nodes: Set[str]

        def __init__(self):
            self.reset()

        def reset(self):
            self.name = None
            self.nodes = set()

    current_fn: CurrentFunctionInfo = CurrentFunctionInfo()

    def parse_file(functions_input: TextIO) -> Iterable[str]:
        functions = set()

        def need_no_incomplete_fn():
            if current_fn.name is not None and current_fn.nodes:
                raise MalformedFunction(current_fn.name, num, line)

        for num, line in enumerate(functions_input):
            line = line.strip()

            match = function_re.match(line)
            if match is not None:
                need_no_incomplete_fn()
                if match['name'] in functions:
                    raise DuplicateFunction(match['name'], num, line)
                functions.add(match['name'])
                # Skip empty functions
                current_fn.name = match['name']
                continue

            def unexpected():
                raise UnexpectedInput(num, line)

            def need_current_fn():
                if current_fn.name is None:
                    unexpected()

            def need_no_current_fn():
                if current_fn.name is not None:
                    unexpected()

            def add_node(label: str):
                need_current_fn()
                if label in current_fn.nodes:
                    raise DuplicateNode(current_fn.name, label)
                current_fn.nodes.add(label)

            match = basic_re.match(line)
            if match is not None:
                add_node(match['label'])
                continue
            match = call_re.match(line)
            if match is not None:
                add_node(match['label'])
                continue
            match = cond_re.match(line)
            if match is not None:
                add_node(match['label'])
                continue

            match = entry_re.fullmatch(line)
            if match is not None:
                need_current_fn()
                if match['entry'] not in current_fn.nodes:
                    raise MalformedFunction(current_fn.name, num, line)
                assert current_fn.name is not None
                yield current_fn.name
                current_fn.reset()
                continue

            if structs:
                match = struct_re.match(line)
                if match is not None:
                    need_no_current_fn()
                    continue

            if line != '':
                unexpected()

        need_no_incomplete_fn()

    with open(functions_file) as functions:
        yield from parse_file(functions)


def c_function_name(name: str) -> str:
    assert name.startswith('Kernel_C.')
    name = name[len('Kernel_C.'):]
    if name.startswith("StrictC'"):
        return name[len("strictC'"):]
    return name


def common_functions(path: Path) -> Sequence[str]:
    asm_functions = set(parse_functions(path / 'ASMFunctions.txt', structs=False))
    c_functions = set(map(c_function_name, parse_functions(path / 'CFunctions.txt', structs=True)))
    return sorted(asm_functions & c_functions)


def main(args) -> None:
    [_, path] = args
    for f in common_functions(Path(path)):
        print(f)


if __name__ == '__main__':
    main(sys.argv)
