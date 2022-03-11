#!/usr/bin/env python3

# Copyright (c) 2022, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# A toolkit for building, installing and distributing the decompiler.

import argparse
import os
import shutil
import signal
import subprocess
import sys

from pathlib import Path
from typing import NamedTuple, Protocol

STATUS_SIGNAL_OFFSET = 128
STATUS_USAGE = 1

# We currently always install decompiler artifcats in a fixed location
# relative to the graph-refine repository root.
decompiler_dir = Path(__file__).resolve().parent
decompile = decompiler_dir / 'decompile'

hol4_source_dir = decompiler_dir / 'src' / 'HOL4'
polyml_source_dir = decompiler_dir / 'src' / 'polyml'
polyml_install_dir = decompiler_dir / 'install' / 'polyml'

# File/link names relative to `decompiler_dir`:
decompile_local = Path('decompile.py')
decompile_docker = Path('decompile-docker.py')
decompile_nix = Path('decompile-nix')

seL4_branch = 'seL4-decompiler'


class Repo(Protocol):
    def url(self, ssh: bool) -> str:
        ...


class GitHub(NamedTuple):
    repo: str

    def url(self, ssh: bool) -> str:
        return f'git@github.com:{self.repo}.git' if ssh else f'https://github.com/{self.repo}.git'


class Branch(NamedTuple):
    repo: Repo
    branch: str


class Source(NamedTuple):
    upstream: Branch
    fork: Branch
    checkout_dir: Path


hol4_source = Source(upstream=Branch(repo=GitHub('HOL-Theorem-Prover/HOL'), branch='master'),
                     fork=Branch(repo=GitHub('seL4/HOL'), branch=seL4_branch),
                     checkout_dir=hol4_source_dir)

polyml_source = Source(upstream=Branch(repo=GitHub('polyml/polyml'), branch='master'),
                       fork=Branch(repo=GitHub('seL4/polyml'), branch=seL4_branch),
                       checkout_dir=polyml_source_dir)


class CheckoutPhase(Protocol):
    def do_checkout(self) -> None:
        ...


def rm_path(*paths: Path) -> None:
    for p in paths:
        if p.is_symlink():
            os.unlink(p)
        if p.is_dir():
            shutil.rmtree(p)
        elif p.exists():
            os.unlink(p)


def check_empty(*paths: Path) -> None:
    non_empty_paths = [p for p in paths if p.exists()]
    if non_empty_paths:
        sys.stderr.write(
            'decompiler-setup: paths should not exist when using --checkout without --force:\n')
        for p in non_empty_paths:
            sys.stderr.write(f'  {p}\n')
        sys.stderr.flush()
        exit(STATUS_USAGE)


def check_exists(*paths: Path) -> None:
    paths_not_exist = [p for p in paths if not p.is_dir()]
    if paths_not_exist:
        sys.stderr.write(
            'decompiler-setup: paths should already exist when not using --checkout:\n')
        for p in paths_not_exist:
            sys.stderr.write(f'  {p}\n')
        sys.stderr.flush()
        exit(STATUS_USAGE)


def checkout_source(source: Source, ssh: bool) -> None:
    source.checkout_dir.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(['git', 'clone', '-q', '-b', source.fork.branch,
                    source.fork.repo.url(ssh), source.checkout_dir],
                   cwd=decompiler_dir, stdin=subprocess.DEVNULL, check=True)
    subprocess.run(['git', 'remote', 'add', 'upstream', source.upstream.repo.url(ssh)],
                   cwd=source.checkout_dir, stdin=subprocess.DEVNULL, check=True)
    subprocess.run(['git', 'fetch', '-q', 'upstream'],
                   cwd=source.checkout_dir, stdin=subprocess.DEVNULL, check=True)


def upstream_source(source: Source) -> None:
    subprocess.run(['git', 'merge', '-q', '-m', 'merge upstream', f'upstream/{source.upstream.branch}'],
                   cwd=source.checkout_dir, stdin=subprocess.DEVNULL, check=True)


class CheckoutSources(NamedTuple):
    checkout: bool
    upstream: bool
    force: bool
    ssh: bool

    def github_url(self, repo) -> str:
        return f'git@github.com:{repo}.git' if self.ssh else f'https://github.com/{repo}.git'

    def do_checkout(self) -> None:
        if (self.force or self.upstream) and not self.checkout:
            sys.stderr.write(
                'decompiler-setup: --upstream and --force only makes sense with --checkout\n')
            sys.stderr.flush()
            exit(STATUS_USAGE)
        if not self.checkout:
            check_exists(hol4_source_dir, polyml_source_dir)
            return
        if self.force:
            rm_path(hol4_source_dir, polyml_source_dir)
        if self.checkout:
            check_empty(hol4_source_dir, polyml_source_dir)
            for source in [hol4_source, polyml_source]:
                checkout_source(source, self.ssh)
        if self.upstream:
            for source in [hol4_source, polyml_source]:
                upstream_source(source)


class CheckoutNone(NamedTuple):
    def do_checkout(self) -> None:
        # Nothing to do here.
        pass


class InstallPhase(Protocol):
    def do_install(self) -> None:
        ...


class InstallNone(NamedTuple):
    def do_install(self) -> None:
        # Nothing to do here.
        pass


def rm_decompiler_setup() -> None:
    rm_path(decompile, decompiler_dir / decompile_nix)


# This is mainly intended for initial installation of the decompiler,
# and not for incremental development on HOL4 or the decompiler.
# If you're working on the decompiler, we assume you know how to use Holmake.
class InstallLocal(NamedTuple):
    def do_install(self) -> None:
        rm_decompiler_setup()
        rm_path(polyml_install_dir)
        # PolyML
        subprocess.run(['git', 'clean', '-fdX'],
                       cwd=polyml_source_dir, stdin=subprocess.DEVNULL, check=True)
        subprocess.run(['./configure', f'--prefix={polyml_install_dir}'],
                       cwd=polyml_source_dir, stdin=subprocess.DEVNULL, check=True)
        subprocess.run(['make'], cwd=polyml_source_dir, stdin=subprocess.DEVNULL, check=True)
        subprocess.run(['make', 'install'], cwd=polyml_source_dir,
                       stdin=subprocess.DEVNULL, check=True)
        poly = polyml_install_dir / 'bin' / 'poly'
        # HOL4
        subprocess.run(['git', 'clean', '-fdX'],
                       cwd=hol4_source_dir, stdin=subprocess.DEVNULL, check=True)
        with open(hol4_source_dir / 'tools' / 'smart-configure.sml') as configure:
            subprocess.run([poly], cwd=hol4_source_dir, stdin=configure, check=True)
        subprocess.run([hol4_source_dir / 'bin' / 'build'],
                       cwd=hol4_source_dir, stdin=subprocess.DEVNULL, check=True)
        # Decompiler
        PATH = os.environ['PATH']
        decompiler_src = hol4_source_dir / 'examples' / 'machine-code' / 'graph'
        env = {**os.environ, 'PATH': f'{hol4_source_dir}/bin:{PATH}'}
        subprocess.run(['Holmake'], env=env, cwd=decompiler_src,
                       stdin=subprocess.DEVNULL, check=True)
        # Script
        os.symlink(decompile_local, decompile)


class InstallNix(NamedTuple):
    def do_install(self) -> None:
        rm_decompiler_setup()
        subprocess.run(['nix-build', '-A', 'decompiler', '-o', decompile_nix],
                       cwd=decompiler_dir, stdin=subprocess.DEVNULL, check=True)
        os.symlink(decompile_nix / 'bin' / 'decompile', decompile)


class InstallDocker(NamedTuple):
    def do_install(self) -> None:
        rm_decompiler_setup()
        subprocess.run(['docker', 'pull', 'ghcr.io/sel4/decompiler:latest'],
                       stdin=subprocess.DEVNULL, check=True)
        os.symlink(decompile_docker, decompile)


class SetupCommand(NamedTuple):
    checkout: CheckoutPhase
    install: InstallPhase

    def do_setup(self) -> None:
        self.checkout.do_checkout()
        self.install.do_install()


def parse_args() -> SetupCommand:
    parser = argparse.ArgumentParser(description='Set up the decompiler.')

    checkout_opt = argparse.ArgumentParser(add_help=False)
    checkout_opt.add_argument('--checkout', action='store_true', dest='checkout',
                              help='Clone source repositories.')

    checkout_extra = argparse.ArgumentParser(add_help=False)
    checkout_extra.add_argument('--upstream', action='store_true', dest='upstream',
                                help='Merge upstream changes.')
    checkout_extra.add_argument('--force', action='store_true', dest='force',
                                help='Replace an existing checkout with a new one.')
    checkout_extra.add_argument('--ssh', action='store_true', dest='ssh',
                                help='Use SSH when cloning from GitHub.')

    subparsers = parser.add_subparsers(required=True, dest='command')
    checkout_cmd = subparsers.add_parser('checkout', parents=[checkout_extra],
                                         help='Clone source repositories, but do not install.')
    local_cmd = subparsers.add_parser('local', parents=[checkout_opt, checkout_extra],
                                      help='Install decompiler built locally.')
    nix_cmd = subparsers.add_parser('nix', parents=[checkout_opt, checkout_extra],
                                    help='Install decompiler built using Nix.')
    docker_cmd = subparsers.add_parser('docker', help='Install decompiler from Docker.')

    def require_checkout(args) -> CheckoutPhase:
        return CheckoutSources(checkout=args.checkout,
                               upstream=args.upstream,
                               force=args.force,
                               ssh=args.ssh)

    def no_checkout(args) -> CheckoutPhase:
        return CheckoutNone()

    checkout_cmd.set_defaults(checkout=True,
                              checkout_phase=require_checkout, install_phase=InstallNone)
    local_cmd.set_defaults(checkout_phase=require_checkout, install_phase=InstallLocal)
    nix_cmd.set_defaults(checkout_phase=require_checkout, install_phase=InstallNix)
    docker_cmd.set_defaults(checkout_phase=no_checkout, install_phase=InstallDocker)

    args = parser.parse_args()

    return SetupCommand(checkout=args.checkout_phase(args),
                        install=args.install_phase())


def main(setup_command: SetupCommand) -> int:
    try:
        setup_command.do_setup()
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
