#!/usr/bin/env python3

# Copyright (c) 2022, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import itertools
import mmap
import os
import subprocess
import sys
import textwrap

from pathlib import Path
from typing import NamedTuple, Protocol


def unlines(*lines: str) -> str:
    return ''.join(f'{line}\n' for line in lines)


# We need to see this exact text printed near the end of the output.
check_text = textwrap.dedent('''\
    Proving correctness of call offsets
    ===================================

    Offsets proved correct.

    Summary
    =======

    No stack intro failures.
    No graph spec failures.
    No export failures.
    No call offset failures.
''').encode()


def output_ok(output_filename: str) -> bool:
    with open(output_filename, 'rb') as output:
        with mmap.mmap(output.fileno(), 0, prot=mmap.PROT_READ) as buff:
            return buff.find(check_text) > 0


class Decompile(Protocol):
    def decompile(self) -> None:
        ...


class Args(NamedTuple):
    filename_prefix: Path
    fast: bool
    ignore: str


class DecompileLocal(NamedTuple):
    hol4_src: str
    args: Args

    def hol_input(self) -> bytes:
        args = self.args
        fast_str = 'true' if args.fast else 'false'
        text = unlines(f'val _ = load "decompileLib";',
                       f'val _ = decompileLib.decomp "{args.filename_prefix}" {fast_str} "{args.ignore}";')
        return text.encode()

    def decompile(self) -> None:
        decompiler_src = self.hol4_src / 'examples' / 'machine-code' / 'graph'
        hol4_bin = self.hol4_src / 'bin'
        hol4_exe = hol4_bin / 'hol'
        PATH = os.environ['PATH']
        env = {**os.environ, 'PATH': f'{hol4_bin}:{PATH}'}
        output_file = f'{self.args.filename_prefix}_output.txt'
        subprocess.run(f'{hol4_exe} 2>&1 | tee {output_file}', shell=True, cwd=decompiler_src, env=env,
                       input=self.hol_input(), check=True)
        assert output_ok(output_file)


class DecompileDocker(NamedTuple):
    command: str
    image: str
    args: Args

    def decompile(self) -> None:
        target_dir = self.args.filename_prefix.parent
        cmd = [self.command, 'run', '--rm', '-i',
               '--mount', f'type=bind,source={target_dir},dst=/target',
               '--mount', 'type=tmpfs,dst=/tmp',
               self.image, f'/target/{self.args.filename_prefix.name}']
        if self.args.fast:
            cmd.append('--fast')
        if self.args.ignore:
            cmd.extend(['--ignore', self.args.ignore])
        subprocess.run(cmd, cwd=target_dir, stdin=subprocess.DEVNULL, check=True)


def parse_args() -> Decompile:
    parser = argparse.ArgumentParser(description='Run the decompiler.')
    parser.add_argument('filename', metavar='FILENAME', type=str,
                        help='input filename prefix, e.g. /path/to/example for /path/to/example.elf.txt')
    parser.add_argument('--fast', action='store_true', dest='fast',
                        help='skip some proofs')
    parser.add_argument('--ignore', metavar='NAMES', type=str, action='append',
                        help='functions to ignore (comma-separated list)')
    # For internal use only.
    parser.add_argument('--docker', metavar='COMMAND', help=argparse.SUPPRESS)

    parsed_args = parser.parse_args()

    # Combine multiple ignore options
    ignore_gen = (i for j in (parsed_args.ignore or []) for i in j.split(',') if i)
    ignore = ','.join({i: None for i in ignore_gen}.keys())

    args = Args(filename_prefix=Path(parsed_args.filename).resolve(),
                fast=parsed_args.fast,
                ignore=ignore)

    if parsed_args.docker:
        image = os.environ.get('DECOMPILER_DOCKER_IMAGE', 'ghcr.io/sel4/decompiler:latest')
        return DecompileDocker(command=parsed_args.docker, image=image, args=args)

    hol4_dir = os.environ.get('HOL4_DIR')
    if hol4_dir is None:
        hol4_path = Path(__file__).resolve().parent / 'src' / 'HOL4'
    else:
        hol4_path = Path(hol4_dir).resolve()

    return DecompileLocal(hol4_src=hol4_path, args=args)


def main(decompile: Decompile):
    try:
        decompile.decompile()
        return 0
    except KeyboardInterrupt:
        return STATUS_SIGNAL_OFFSET + signal.SIGINT
    except BrokenPipeError:
        # Our output was closed early, e.g. we were piped to `less` and the user quit
        # before we finished. If sys.stdout still has unwritten characters its buffer
        # that it can't write to the closed file descriptor, then the interpreter prints
        # an ugly warning to sys.stderr as it shuts down. We assume we don't care, so
        # close sys.stderr to suppress the warning.
        sys.stderr.close()
        return STATUS_SIGNAL_OFFSET + signal.SIGPIPE


if __name__ == '__main__':
    exit(main(parse_args()))
