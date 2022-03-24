#!/usr/bin/env python3

# Copyright (c) 2022, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import fcntl
import os
import time
import random
import subprocess
import sys

from contextlib import contextmanager
from pathlib import Path
from typing import Callable, ContextManager, Dict, Iterator, List, NamedTuple, Sequence, Union


class Config(NamedTuple):
    name: str
    path: Path
    arch: str


class QueuedFunction(NamedTuple):
    config: Config
    name: str

    def move_to_working(self) -> None:
        from_path = self.config.path / 'waiting' / self.name
        to_path = self.config.path / 'working' / self.name
        from_path.rename(to_path)


class RunningFunction(NamedTuple):
    queued: QueuedFunction
    proc: subprocess.Popen

    def remove_working(self) -> None:
        working_path = self.queued.config.path / 'working' / self.queued.name
        working_path.unlink()


class Job(NamedTuple):
    job_dir: Path
    smt2_dir: Path
    graph_refine: Path
    concurrency: int
    configs: Sequence[Config]
    waiting: List[QueuedFunction]
    running: Dict[int, RunningFunction]

    def pick_waiting(self) -> QueuedFunction:
        picked = self.waiting.pop()
        picked.move_to_working()
        return picked

    def start_function(self) -> None:
        function = self.pick_waiting()
        fun_dir = function.config.path / 'functions' / function.name
        fun_dir.mkdir(parents=True, exist_ok=True)
        report_path = fun_dir / 'report.txt'
        cmd: List[Union[Path, str]] = [self.graph_refine,
                                       function.config.path / 'target',
                                       f'trace-to:{report_path}',
                                       function.name]
        env = {**os.environ,
               'L4V_ARCH': function.config.arch,
               'GRAPH_REFINE_SMT2_DIR': f'{self.smt2_dir}'}
        with open(fun_dir / 'log.txt', 'w') as log_file:
            proc = subprocess.Popen(cmd, cwd=fun_dir, env=env,
                                    stdin=subprocess.DEVNULL,
                                    stdout=log_file,
                                    stderr=subprocess.STDOUT)
        running = RunningFunction(queued=function, proc=proc)
        self.running[proc.pid] = running

    def run(self) -> None:
        random.shuffle(self.waiting)
        while self.waiting and len(self.running) < self.concurrency:
            self.start_function()
        while self.running:
            pid, ret = os.wait()
            if pid in self.running:
                self.running[pid].remove_working()
                del self.running[pid]
                if self.waiting:
                    self.start_function()


def arch_of(config: str) -> str:
    return config[:config.find('-')]


class Worker(NamedTuple):
    work_dir: Path
    concurrency: int
    graph_refine: Path

    def lock(self, name: str, *, block: bool) -> ContextManager[bool]:
        lock_dir = self.work_dir / 'locks'

        @contextmanager
        def impl() -> Iterator[bool]:
            lock_dir.mkdir(parents=True, exist_ok=True)
            with open(lock_dir / f'{name}.lock', 'w') as lock_file:
                try:
                    block_op = 0 if block else fcntl.LOCK_NB
                    fcntl.flock(lock_file, fcntl.LOCK_EX | block_op)
                    yield True
                except BlockingIOError:
                    yield False

        return impl()

    def list_configs(self, configs_dir: Path) -> Iterator[str]:
        # Initially limit ourselves to RISCV64.
        return (entry.name
                for entry in os.scandir(configs_dir)
                if arch_of(entry.name) == 'RISCV64')

    def initialise_job(self, job_id: str) -> None:
        configs_dir = self.work_dir / 'jobs' / job_id / 'configs'
        for config_name in self.list_configs(configs_dir):
            config_dir = configs_dir / config_name
            waiting_dir = config_dir / 'waiting'
            waiting_dir.mkdir(exist_ok=True)

            with open(config_dir / 'target' / 'functions.txt') as functions:
                for function_name in functions:
                    function_name = function_name.strip()
                    # To track the status of functions, we move files between
                    # directories. Files are empty, but named after functions.
                    # The directory that contains it tells us the state of the
                    # function. All functions are initially waiting.
                    with open(waiting_dir / function_name, 'w'):
                        pass

    def work_job(self, job_id: str) -> None:
        job_dir = self.work_dir / 'jobs' / job_id
        configs_dir = job_dir / 'configs'

        def mk_config(name: str) -> Config:
            path = configs_dir / name
            arch = arch_of(name)
            return Config(name=name, path=path, arch=arch)

        configs = [mk_config(config) for config in self.list_configs(configs_dir)]

        # Create directories needed by the job runner.
        # Move working jobs back to waiting, in case a previous attempt to run
        # this job was interrupted.
        for config in configs:
            working_dir = config.path / 'working'
            waiting_dir = config.path / 'waiting'
            working_dir.mkdir(exist_ok=True)
            waiting_dir.mkdir(exist_ok=True)
            for name in list(entry.name for entry in os.scandir(working_dir)):
                (working_dir / name).rename(waiting_dir / name)

        smt2_dir = self.work_dir / 'smt2'
        smt2_dir.mkdir(exist_ok=True)

        waiting = [QueuedFunction(config=config, name=entry.name)
                   for config in configs
                   for entry in os.scandir(config.path / 'waiting')]

        job = Job(job_dir=job_dir,
                  smt2_dir=smt2_dir,
                  graph_refine=self.graph_refine,
                  concurrency=self.concurrency,
                  configs=configs,
                  waiting=waiting,
                  running={})
        job.run()

        for config in configs:
            (config.path / 'working').rmdir()
            (config.path / 'waiting').rmdir()

    def run_once(self) -> bool:
        queue_dir = self.work_dir / 'queue'
        initialising_path = queue_dir / 'initialising.job'
        working_path = queue_dir / 'working.job'
        # If we're not currently working on a job, try to get one from the queue.
        if not (initialising_path.exists() or working_path.exists()):
            with self.lock('queue', block=True):
                queued_path = queue_dir / 'queued.job'
                # The queue has at most one job.
                if queued_path.exists():
                    queued_path.rename(initialising_path)
        # If we're currently initialising a job, finish initialising it. We
        # separate initialisation from working to ensure that all functions get
        # added to the waiting queue before we start work, even if the process
        # is interrupted before it finishes creating the waiting queue.
        if initialising_path.exists():
            with open(initialising_path) as initialising_file:
                job_id = initialising_file.read().strip()
            self.initialise_job(job_id)
            initialising_path.rename(working_path)
        # If we currently have a working job, continue working on it.
        if working_path.exists():
            with open(working_path) as working_file:
                job_id = working_file.read().strip()
            self.work_job(job_id)
            working_path.unlink()
            return True
        # We didn't do any work.
        return False

    def run(self) -> None:
        with self.lock('worker', block=False) as worker_locked:
            # If we didn't get a lock, there is already a worker running.
            if worker_locked:
                while True:
                    did_work = self.run_once()
                    if not did_work:
                        time.sleep(30)


def parse_args():

    def path_test(test: Callable[[str], bool], desc: str) -> Callable[[str], Path]:
        def do_test(path: str) -> Path:
            if test(path):
                return Path(path).resolve()
            else:
                raise argparse.ArgumentTypeError(f'{path} is not a valid {desc}')
        return do_test

    parser = argparse.ArgumentParser(description='Run graph-refine jobs')
    parser.add_argument('--concurrency', metavar='N', type=int, required=True,
                        help='Number of function analyses to run in parallel')
    parser.add_argument('--work-dir', metavar='DIR', required=True,
                        type=path_test(os.path.isdir, 'directory name'),
                        help='Root of graph-refine work directory')
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    def is_valid_script(path: str) -> bool:
        return os.path.isfile(path) and os.access(path, os.R_OK | os.X_OK)

    def error_msg(msg: str) -> None:
        print(f'error: graph-refine-parallel: {msg}', file=sys.stderr)

    graph_refine = os.environ.get('GRAPH_REFINE_SCRIPT')
    if graph_refine is None:
        error_msg('GRAPH_REFINE_SCRIPT was not set')
        sys.exit(1)
    if not is_valid_script(graph_refine):
        error_msg('GRAPH_REFINE_SCRIPT is not executable')
        sys.exit(1)

    worker = Worker(work_dir=args.work_dir,
                    concurrency=args.concurrency,
                    graph_refine=Path(graph_refine))
    worker.run()


if __name__ == '__main__':
    main()
