#!/usr/bin/env python3

# Print a list of functions from ASMFunctions.txt, sorted by
# number of nodes in the function graph, possibly filtered by
# various criteria.
#
# For usage information, run:
#   sort_by_size.py --help

import math
import re
from argparse import ArgumentParser, FileType
from typing import Sequence

def parse_arguments():
    parser = ArgumentParser(description='List functions ordered by graph size')
    parser.add_argument('-i', '--include-only', metavar='FILE', type=FileType(),
                        help='ignore functions not listed in FILE')
    parser.add_argument('-l', '--low-bound', metavar='n', type=int,
                        help='only show functions with at least n nodes')
    parser.add_argument('-u', '--high-bound', metavar='n', type=int,
                        help='only show functions with at most n nodes')
    parser.add_argument('--with-calls', action='store_const', dest='calls', const=True,
                        help='only show functions with Call nodes')
    parser.add_argument('--without-calls', action='store_const', dest='calls', const=False,
                        help='only show functions without Call nodes')
    parser.add_argument('--with-loops', action='store_const', dest='loops', const=True,
                        help='only show functions with loops')
    parser.add_argument('--without-loops', action='store_const', dest='loops', const=False,
                        help='only show functions without loops')
    parser.add_argument('-c', '--show-counts', action='store_true',
                        help='show number of nodes for each listed function')
    parser.add_argument('ASMFunctions', type=FileType(),
                        help='GraphLang input file')
    return parser.parse_args()

def get_include_fn(include_only_file):
    if include_only_file is None:
        return lambda _: True
    try:
        include_set = set(s.strip() for s in include_only_file)
        return lambda f: f in include_set
    finally:
        include_only_file.close()

def has_loops(node, arcs):
    current = set()
    clear = set()

    class HasLoop(Exception):
        pass

    def visit(n):
        current.add(n)
        for v in arcs.get(n, set()):
            if v in current:
                raise HasLoop
            if v not in clear:
                visit(v)
        current.remove(n)
        clear.add(n)

    try:
        visit(node)
    except HasLoop:
        return True
    return False


class UnexpectedInput(Exception):
    pass


def analyse_fns(fns_file, include, calls, loops):
    fns_by_size = {}

    class FnData:
        def __init__(self):
            self.reset()

        def reset(self):
            self.name = None
            self.has_calls = False
            self.entry = None
            self.arcs = {}

        def nodes(self):
            return len(self.arcs)

    current_fn = FnData()

    def try_add_current_fn():
        if current_fn.name is None or not include(current_fn.name):
            return
        if calls is not None and current_fn.has_calls != calls:
            return
        if loops is not None and has_loops(current_fn.entry, current_fn.arcs) != loops:
            return
        fns_for_size = fns_by_size.setdefault(current_fn.nodes(), set())
        fns_for_size.add(current_fn.name)

    def add_current_fn():
        try:
            try_add_current_fn()
        finally:
            current_fn.reset()

    function_re = re.compile(r'Function (?P<name>\S+)')
    node_re = re.compile(r'(?P<addr>\w+) (?P<typ>Basic|Call|Cond) (?P<succ>\w+) (?P<alt>\w+)')
    entry_re = re.compile(r'EntryPoint (?P<entry>\w+)')

    def parse_file():
        for line in fns_file:
            line = line.strip()
            fn_match = function_re.match(line)
            if fn_match is not None:
                add_current_fn()
                current_fn.name = fn_match['name']
                continue
            node_match = node_re.match(line)
            if node_match is not None:
                addr, typ, succ, alt = node_match.group('addr', 'typ', 'succ', 'alt')
                current_fn.arcs[addr] = {succ, alt} if typ == 'Cond' else {succ}
                current_fn.has_calls = current_fn.has_calls or typ == 'Call'
                continue
            entry_match = entry_re.fullmatch(line)
            if entry_match is not None:
                current_fn.entry = entry_match['entry']
                continue
            if line != '':
                raise UnexpectedInput(line)
        add_current_fn()

    try:
        parse_file()
        return fns_by_size
    finally:
        fns_file.close()

def print_fns(fn_data, low, hi, show_counts):
    counts = fn_data.keys()
    if low is not None:
        counts = filter(lambda c: low <= c, counts)
    if hi is not None:
        counts = filter(lambda c: c <= hi, counts)
    if not counts:
        return
    counts = sorted(counts)
    count_width = math.floor(math.log10(counts[-1])) + 1
    for count in counts:
        for fn in sorted(fn_data[count]):
            if show_counts:
                print(f'{count:{count_width}} {fn}')
            else:
                print(f'{fn}')

def main():
    args = parse_arguments()
    include_fn = get_include_fn(args.include_only)
    fn_data = analyse_fns(args.ASMFunctions, include=include_fn,
                          calls=args.calls, loops=args.loops)
    print_fns(fn_data=fn_data, low=args.low_bound, hi=args.high_bound,
              show_counts=args.show_counts)

if __name__ == '__main__':
    main()
