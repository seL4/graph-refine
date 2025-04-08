#!/usr/bin/env python3

# Copyright 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

# Calculate a hash of a directory tree, using file and directory names and
# contents. Used to uniquely identify graph-refine jobs in CI.

import os
import sys

from base64 import b32encode
from hashlib import blake2b
from pathlib import Path
from typing import Sequence


def dir_entry_name(entry: os.DirEntry) -> str:
    return entry.name


def hash_dir(path: Path) -> bytes:
    hasher = blake2b(person=b'dir contents')
    for entry in sorted(os.scandir(path), key=dir_entry_name):
        hasher.update(blake2b(entry.name.encode(), person=b'dir entry').digest())
        hasher.update(hash_dir_entry(path, entry))
    return hasher.digest()


def hash_file(path: Path) -> bytes:
    hasher = blake2b(person=b'file contents')
    with open(path, 'rb') as file:
        while chunk := file.read(2 ** 10):
            hasher.update(chunk)
    return hasher.digest()


def hash_symlink(path: Path) -> bytes:
    return blake2b(os.readlink(path).encode(), person=b'symlink target').digest()


class UnknownEntryType(Exception):
    pass


def hash_dir_entry(parent_path: Path, entry: os.DirEntry) -> bytes:
    path = parent_path / entry.name
    if entry.is_symlink():
        return hash_symlink(path)
    if entry.is_dir():
        return hash_dir(path)
    if entry.is_file():
        return hash_file(path)
    raise UnknownEntryType(path)


def hash_path(path: Path) -> bytes:
    if path.is_symlink():
        return hash_symlink(path)
    if path.is_dir():
        return hash_dir(path)
    if path.is_file():
        return hash_file(path)
    raise FileNotFoundError(path)


def hash_path_b32(path: str) -> str:
    path_hash = blake2b(hash_path(Path(path)), digest_size=20).digest()
    return b32encode(path_hash).decode().lower().rstrip('=')


def main(args: Sequence[str]) -> None:
    [_, path] = args
    print(hash_path_b32(path))


if __name__ == '__main__':
    main(sys.argv)
