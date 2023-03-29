#!/usr/bin/env python3

import argparse
import enum
import fcntl
import json
import os
import queue
import random
import re
import shutil
import signal
import sqlite3
import string
import subprocess
import sys
import threading
import time

from base64 import b32encode
from contextlib import contextmanager, redirect_stdout, redirect_stderr
from dataclasses import dataclass
from datetime import datetime, timezone
from hashlib import blake2b
from pathlib import Path
from typing import (Any, Callable, ContextManager, Iterable, Iterator, Mapping, NamedTuple,
                    Optional, Protocol, Sequence, TypeVar)


K = TypeVar('K')
T = TypeVar('T')
U = TypeVar('U')
V = TypeVar('V')


def now_utc() -> datetime:
    return datetime.now(tz=timezone.utc)


# Date/time format used by SQLite.
def sqlite_timestamp(timestamp: datetime) -> str:
    return f'{timestamp:%Y-%m-%dT%H:%M:%SZ}'


dev_random = random.SystemRandom()
rand_chars = string.ascii_lowercase + string.digits


# Unique IDs for naming runner instances, and function analysis result directories.
def mk_unique_id(timestamp: Optional[datetime] = None) -> str:
    if timestamp is None:
        timestamp = now_utc()
    extra = ''.join(dev_random.choice(rand_chars) for i in range(20))
    return f'{timestamp:%Y-%m-%d-%H-%M-%S}-{extra}'


def write_log(msg: str, *msgs: str) -> None:
    date_fmt = "%Y-%m-%d %H:%M:%S"
    timestamp = f'{datetime.now(tz=timezone.utc):%Y-%m-%d %H:%M:%S}'
    print(f'{timestamp}: {msg}')
    for msg in msgs:
        print(f'{timestamp}: {msg}')
    sys.stdout.flush()


# Filesyste layout
# ----------------
#
# WORK_DIR/
#
#   public/
#     jobs.json - list of running, waiting and recently completed jobs.
#     jobs/
#       JOB_ID/
#         targets.json - summary status for each target.
#         targets/
#           TARGET_ID/
#             target/
#               functions-list.txt, ...
#             functions.json - status of each task in the target.
#             functions/
#               FUNCTION_NAME/
#                 UNIQUE_RUN_ID/
#                   report.txt
#                   log.txt
#                   exit_code.txt
#
#     runners/
#       RUNNER_ID/
#         INSTANCE_ID.log
#
#     smt/
#
#   private/
#     new/
#     jobs.db
#
#     cpus_allowed.txt
#     active_runner_id.txt
#     active_instance.txt
#
#     cpus/
#       CPU_ID/
#         .lock
#
#     runners/
#       RUNNER_ID/
#         .lock


# A task is an individual graph-refine function analysis,
# identified by a triple of job ID, target name and function name.
class Task(NamedTuple):
    job_id: str
    target: str
    function: str


# A simple SQLite database for tracking jobs and tasks.
#
# A job is a collection of targets.
# A target specifies a combination of architecture, seL4 features and optimisation level.
# Each function within a target gives rise to a task.

class WaitingJob(NamedTuple):
    job_id: str
    time_job_submitted: str


class EnqueueTask(NamedTuple):
    task: Task
    priority: int


GetTasksForJob = Callable[[str], Iterable[EnqueueTask]]
EnqueuePriority = Callable[[Task], int]


class TaskRun(NamedTuple):
    job_id: str
    target: str
    function: str
    run_id: str


class JobData(NamedTuple):
    time_job_submitted: str
    time_job_started: Optional[str]
    time_job_finished: Optional[str]


class TaskAssigned(NamedTuple):
    runner_id: str
    run_id: str


class TaskUnassigned(NamedTuple):
    pass


TaskAssignment = TaskAssigned | TaskUnassigned


class RunData(NamedTuple):
    time_run_started: str
    time_run_finished: Optional[str]
    result: Optional[str]


class TaskData(NamedTuple):
    assignment: Optional[TaskAssignment]
    runs: Mapping[TaskAssigned, RunData]


# job_id -> target -> T
TargetMap = Mapping[str, Mapping[str, T]]

# job_id -> JobData
DirtyJobs = Mapping[str, JobData]

# job_id -> target -> status -> count
DirtyTargets = TargetMap[Mapping[str, int]]

# job_id -> target -> function -> TaskData
DirtyTasks = TargetMap[Mapping[str, TaskData]]


class DirtyDbState(NamedTuple):
    jobs: DirtyJobs
    targets: DirtyTargets
    tasks: DirtyTasks
    clean: Callable[[], None]


@enum.unique
class TaskResult(enum.Enum):
    PASSED = enum.auto()
    FAILED = enum.auto()
    NO_SPLIT = enum.auto()
    EXCEPT = enum.auto()
    MALFORMED = enum.auto()
    UNDERSPECIFIED = enum.auto()
    COMPLEX_LOOP = enum.auto()
    NO_RESULT = enum.auto()
    IMPOSSIBLE = enum.auto()
    TIMEOUT = enum.auto()
    KILLED = enum.auto()


passing_task_results = {
    TaskResult.PASSED,
    TaskResult.UNDERSPECIFIED,
    TaskResult.COMPLEX_LOOP,
    TaskResult.IMPOSSIBLE,
}


class JobsDB(NamedTuple):
    conn: sqlite3.Connection
    get_tasks: GetTasksForJob

    def query(self, sql: str, parameters=()) -> ContextManager[sqlite3.Cursor]:
        @contextmanager
        def impl() -> Iterator[sqlite3.Cursor]:
            cursor = self.conn.execute(sql, parameters)
            try:
                yield cursor
            finally:
                cursor.close()

        return impl()

    def execute(self, sql: str, parameters=()) -> None:
        self.conn.execute(sql, parameters).close()

    def executemany(self, sql: str, parameters) -> None:
        self.conn.executemany(sql, parameters).close()

    # Schema versioning and migration is a future problem.
    def initialise(self) -> None:
        self.conn.executescript("""
            BEGIN;

            CREATE TABLE IF NOT EXISTS
                jobs (job_id TEXT PRIMARY KEY NOT NULL,
                      time_job_submitted TEXT NOT NULL,
                      time_job_started TEXT,
                      time_job_finished TEXT,
                      is_job_dirty INTEGER NOT NULL)
                STRICT;

            CREATE TABLE IF NOT EXISTS
                tasks (job_id TEXT NOT NULL,
                       target TEXT NOT NULL,
                       function TEXT NOT NULL,
                       priority INTEGER NOT NULL,
                       runner_id TEXT,
                       run_id TEXT,
                       is_task_dirty INTEGER NOT NULL,
                       PRIMARY KEY (job_id, target, function))
                STRICT;

            CREATE TABLE IF NOT EXISTS
                runs (job_id TEXT NOT NULL,
                      target TEXT NOT NULL,
                      function TEXT NOT NULL,
                      runner_id TEXT NOT NULL,
                      run_id TEXT NOT NULL,
                      time_run_started TEXT NOT NULL,
                      time_run_finished TEXT,
                      result TEXT,
                      is_run_dirty INTEGER NOT NULL,
                      PRIMARY KEY (job_id, target, function, runner_id, run_id))
                STRICT;

            -- Used by enqueue_tasks
            CREATE INDEX IF NOT EXISTS
                jobs_waiting_by_submit_time
                ON jobs (unixepoch(time_job_submitted))
                WHERE time_job_started IS NULL
                  AND time_job_finished IS NULL;

            -- Used by try_assign_tasks
            CREATE INDEX IF NOT EXISTS
                tasks_unassigned_by_priority
                ON tasks (priority)
                WHERE runner_id IS NULL
                   OR run_id IS NULL;

            -- Used by unassign_tasks
            CREATE INDEX IF NOT EXISTS
                tasks_assigned_by_runner_id
                ON tasks (runner_id)
                WHERE runner_id IS NOT NULL
                  AND run_id IS NOT NULL;

            -- USED by export_dirty_state
            CREATE INDEX IF NOT EXISTS
                jobs_dirty
                ON jobs (job_id)
                WHERE is_job_dirty = 1;

            -- USED by export_dirty_state
            CREATE INDEX IF NOT EXISTS
                tasks_dirty
                ON tasks (job_id, target, function)
                WHERE is_task_dirty = 1;

            -- USED by export_dirty_state
            CREATE INDEX IF NOT EXISTS
                runs_dirty
                ON runs (job_id, target, function, runner_id, run_id)
                WHERE is_run_dirty = 1;

            COMMIT;
        """)

    # Move jobs from the `new` directory into the database.
    def add_waiting_jobs(self, jobs: Sequence[WaitingJob]) -> None:
        with self.conn:
            self.execute("BEGIN")
            insert_job = """
                INSERT INTO jobs(job_id, time_job_submitted, is_job_dirty)
                VALUES (:job_id, :time_job_submitted, 1)
                ON CONFLICT DO NOTHING
            """
            self.executemany(insert_job, (job._asdict() for job in jobs))
            self.execute("COMMIT")

    # Enqueue tasks from waiting jobs, until either `wanted` tasks
    # have been enqueued, or there are no more waiting jobs.
    def enqueue_tasks(self, wanted: int, timestamp: str) -> None:
        tasks_enqueued = 0

        def count_tasks(iter: Iterable[T]) -> Iterator[T]:
            nonlocal tasks_enqueued
            for i in iter:
                tasks_enqueued += 1
                yield i

        with self.conn:
            while tasks_enqueued < wanted:
                self.execute("BEGIN")
                next_job_query = """
                    SELECT job_id
                    FROM jobs
                    WHERE time_job_started IS NULL
                      AND time_job_finished IS NULL
                    ORDER BY unixepoch(time_job_submitted) ASC
                    LIMIT 1
                """
                with self.query(next_job_query) as query:
                    job_rows = query.fetchall()
                if not job_rows:
                    break
                job_id = job_rows[0]["job_id"]

                insert_task = """
                    INSERT INTO tasks(job_id, target, function, priority, is_task_dirty)
                    VALUES (:job_id, :target, :function, :priority, 1)
                    ON CONFLICT DO NOTHING
                """
                task_rows = ({**enqueue.task._asdict(), "priority": enqueue.priority}
                             for enqueue in count_tasks(self.get_tasks(job_id)))
                self.executemany(insert_task, task_rows)

                update_job_status = """
                    UPDATE jobs
                    SET time_job_started = :time_job_started,
                        is_job_dirty = 1
                    WHERE job_id = :job_id
                """
                args = {"job_id": job_id, "time_job_started": timestamp}
                self.execute(update_job_status, args)
                self.execute("COMMIT")

    # Assign tasks to a runner.
    def try_assign_tasks(self, *, runner_id: str, run_id: str, wanted: int,
                         timestamp: str) -> list[TaskRun]:

        def mk_task(row) -> TaskRun:
            return TaskRun(job_id=row["job_id"],
                           target=row["target"],
                           function=row["function"],
                           run_id=run_id)

        def mk_run_row(task: TaskRun) -> dict[str, str]:
            return {**task._asdict(), "runner_id": runner_id, "time_run_started": timestamp}

        with self.conn:
            self.execute("BEGIN")
            assign_tasks_query = """
                UPDATE tasks
                SET runner_id = :runner_id,
                    run_id = :run_id,
                    is_task_dirty = 1
                WHERE rowid IN (SELECT rowid
                                FROM tasks AS t
                                WHERE runner_id IS NULL
                                   OR run_id IS NULL
                                   OR NOT EXISTS (SELECT * FROM runs
                                                  WHERE runs.job_id = t.job_id
                                                    AND runs.target = t.target
                                                    AND runs.function = t.function
                                                    AND runs.runner_id = t.runner_id
                                                    AND runs.run_id = t.run_id)
                                ORDER BY priority ASC, random()
                                LIMIT :wanted)
                RETURNING job_id, target, function
            """
            args = {"runner_id": runner_id, "run_id": run_id, "wanted": wanted}
            with self.query(assign_tasks_query, args) as query:
                tasks = [mk_task(row) for row in query]

            insert_run = """
                INSERT INTO runs(job_id, target, function, runner_id, run_id,
                                 time_run_started, is_run_dirty)
                VALUES (:job_id, :target, :function, :runner_id, :run_id, :time_run_started, 1)
                ON CONFLICT DO NOTHING
            """
            self.executemany(insert_run, (mk_run_row(task) for task in tasks))
            self.execute("COMMIT")
            return tasks

    # Assign tasks to a runner, enqueueing if necessary.
    def assign_tasks(self, runner_id: str, wanted: int) -> Sequence[TaskRun]:
        now = now_utc()
        timestamp = sqlite_timestamp(now)
        run_id = mk_unique_id(now)

        tasks = self.try_assign_tasks(runner_id=runner_id,
                                      run_id=run_id,
                                      wanted=wanted,
                                      timestamp=timestamp)

        wanted -= len(tasks)
        if wanted > 0:
            self.enqueue_tasks(wanted, timestamp)
            tasks += self.try_assign_tasks(runner_id=runner_id,
                                           run_id=run_id,
                                           wanted=wanted,
                                           timestamp=timestamp)

        return tasks

    # Take back unfinished jobs previously assigned to a runner,
    # for example, if the runner died before completing them.
    def unassign_tasks(self, runner_id: str) -> None:
        with self.conn:
            self.execute("BEGIN")
            unassign_tasks_update = """
                UPDATE tasks
                SET runner_id = NULL,
                    run_id = NULL,
                    is_task_dirty = 1
                WHERE runner_id = :runner_id
                  AND NOT EXISTS (SELECT * FROM runs
                                  WHERE runs.job_id = tasks.job_id
                                    AND runs.target = tasks.target
                                    AND runs.function = tasks.function
                                    AND runs.runner_id = :runner_id
                                    AND runs.run_id = tasks.run_id
                                    AND runs.result IS NOT NULL)
            """
            self.execute(unassign_tasks_update, {"runner_id": runner_id})
            self.execute("COMMIT")

    # Mark a task run as complete.
    def finish_run(self, *, runner_id: str, task: TaskRun, result: TaskResult) -> None:
        timestamp = sqlite_timestamp(now_utc())
        with self.conn:
            self.execute("BEGIN")
            finish_run_update = """
                UPDATE runs
                SET time_run_finished = :time_run_finished,
                    result = :result,
                    is_run_dirty = 1
                WHERE job_id = :job_id
                  AND target = :target
                  AND function = :function
                  AND runner_id = :runner_id
                  AND run_id = :run_id
            """
            args = {**task._asdict(),
                    "runner_id": runner_id,
                    "time_run_finished": timestamp,
                    "result": result.name}
            self.execute(finish_run_update, args)

            finish_job_update = """
                UPDATE jobs
                SET time_job_finished = :time_job_finished,
                    is_job_dirty = 1
                WHERE job_id = :job_id
                  AND time_job_started IS NOT NULL
                  AND NOT EXISTS (SELECT *
                                  FROM tasks NATURAL LEFT JOIN runs
                                  WHERE result IS NULL)
            """
            args = {"job_id": task.job_id,
                    "time_job_finished": timestamp}
            self.execute(finish_job_update, args)
            self.execute("COMMIT")

    # Get the jobs and tasks that have been touched since the last export.
    # Used to create and efficiently update JSON files showing the state of
    # queued and running jobs and tasks, so that they can be made visible
    # via a static website.
    def export_dirty_state(self) -> ContextManager[DirtyDbState]:
        @contextmanager
        def impl() -> Iterator[DirtyDbState]:
            with self.conn:
                self.execute("BEGIN")

                jobs = self.export_dirty_jobs()
                targets = self.export_dirty_targets()
                tasks = self.export_dirty_tasks()

                do_clean = False

                def clean() -> None:
                    nonlocal do_clean
                    do_clean = True

                yield DirtyDbState(jobs=jobs, targets=targets, tasks=tasks, clean=clean)

                if do_clean:
                    self.execute("UPDATE jobs SET is_job_dirty = 0 WHERE is_job_dirty = 1")
                    self.execute("UPDATE tasks SET is_task_dirty = 0 WHERE is_task_dirty = 1")
                    self.execute("UPDATE runs SET is_run_dirty = 0 WHERE is_run_dirty = 1")

                self.execute("COMMIT")

        return impl()

    def export_dirty_jobs(self) -> DirtyJobs:
        jobs_query = """
            SELECT job_id, time_job_submitted, time_job_started, time_job_finished
            FROM jobs
            WHERE is_job_dirty = 1
               OR job_id IN (SELECT job_id FROM tasks WHERE is_task_dirty = 1
                             UNION SELECT job_id FROM runs WHERE is_run_dirty = 1)
        """
        with self.query(jobs_query) as query:
            return {row["job_id"]: JobData(time_job_submitted=row["time_job_submitted"],
                                           time_job_started=row["time_job_started"],
                                           time_job_finished=row["time_job_finished"])
                    for row in query}

    def export_dirty_targets(self) -> DirtyTargets:
        targets_query = """
            SELECT job_id, target,
                   IFNULL((SELECT IFNULL(result, 'RUNNING')
                           FROM runs
                           WHERE runs.job_id = tasks.job_id
                             AND runs.target = tasks.target
                             AND runs.function = tasks.function
                             AND runs.runner_id = tasks.runner_id
                             AND runs.run_id = tasks.run_id),
                          'WAITING')
                   AS status,
                   count(*) AS task_count
            FROM tasks
            WHERE job_id in (SELECT job_id FROM jobs WHERE is_job_dirty = 1
                             UNION SELECT job_id FROM tasks AS t WHERE t.is_task_dirty = 1
                             UNION SELECT job_id FROM runs WHERE is_run_dirty = 1)
            GROUP BY job_id, target, status
        """
        with self.query(targets_query) as query:
            targets: dict[str, dict[str, dict[str, int]]] = {}
            for row in query:
                job = targets.setdefault(row["job_id"], {})
                target = job.setdefault(row["target"], {})
                target[row["status"]] = row["task_count"]

        return targets

    def export_dirty_tasks(self) -> DirtyTasks:
        assignments = self.export_dirty_assignments()
        runs = self.export_dirty_runs()
        tasks: dict[str, dict[str, dict[str, TaskData]]] = {}

        for job_id in assignments.keys() | runs.keys():
            assignments_targets = assignments.get(job_id, {})
            runs_targets = runs.get(job_id, {})
            tasks_targets = tasks.setdefault(job_id, {})

            for target in assignments_targets.keys() | runs_targets.keys():
                assignments_functions = assignments_targets.get(target, {})
                runs_functions = runs_targets.get(target, {})
                tasks_functions = tasks_targets.setdefault(target, {})

                for function in assignments_functions.keys() | runs_functions.keys():
                    assignment = assignments_functions.get(function, None)
                    runs_data = runs_functions.get(function, {})
                    tasks_functions[function] = TaskData(assignment=assignment, runs=runs_data)

        return tasks

    def export_dirty_assignments(self) -> TargetMap[Mapping[str, TaskAssignment]]:
        tasks_query = """
            SELECT job_id, target, function,
                   runs.runner_id AS runner_id,
                   runs.run_id AS run_id
            FROM tasks NATURAL LEFT JOIN runs
            WHERE is_task_dirty = 1
        """
        with self.query(tasks_query) as query:
            assignments: dict[str, dict[str, dict[str, TaskAssignment]]] = {}
            for row in query:
                job = assignments.setdefault(row["job_id"], {})
                target = job.setdefault(row["target"], {})
                target[row["function"]] = \
                    TaskUnassigned() if row["runner_id"] is None or row["run_id"] is None \
                    else TaskAssigned(runner_id=row["runner_id"], run_id=row["run_id"])

        return assignments

    def export_dirty_runs(self) -> TargetMap[Mapping[str, Mapping[TaskAssigned, RunData]]]:
        runs_query = """
            SELECT job_id, target, function, runner_id, run_id,
                   time_run_started, time_run_finished, result
            FROM runs
            WHERE is_run_dirty = 1
        """
        with self.query(runs_query) as query:
            runs: dict[str, dict[str, dict[str, dict[TaskAssigned, RunData]]]] = {}
            for row in query:
                job = runs.setdefault(row["job_id"], {})
                target = job.setdefault(row["target"], {})
                function = target.setdefault(row["function"], {})
                assigned = TaskAssigned(runner_id=row["runner_id"], run_id=row["run_id"])
                function[assigned] = RunData(time_run_started=row["time_run_started"],
                                             time_run_finished=row["time_run_finished"],
                                             result=row["result"])

        return runs


# File locking utilities.
#
# To allow job runners to execute concurrently with each other, and with job
# submission, we use `flock` advisory file locks to control access to shared
# resources.
#
# We use file locks in two ways:
#
# - To ensure uniqueness of certain processes. Each unique process is represented
#   by a lock file that is not otherwise used. On startup, the process makes a
#   non-blocking attempt to lock the file. If successful, the process should hold
#   onto the lock as long as it continues executing. Otherwise, it should exit,
#   since there is already a process running.
#
# - To ensure atomic updates to shared files. For this, we need three files: the
#   file we want to read and update, a separate lock file, and a temporary file to
#   stage the update. We first make a blocking attempt to lock the lock file. When
#   we get the lock, we can read the file and act on its contents. To update it,
#   we write a new version to a temporary file, and then atomically move it to the
#   original file's location. Finally, we can release the lock.
#
# The main differences are whether we block on the attempt to lock the file, and
# whether we hold onto the lock for an extended period.
#
# For updateable files, we use JSON-encoded data, so we build JSON handling into
# the locking protocol. We try not to let these files get too big.


class LockFile(NamedTuple):
    path: Path
    is_locked: Callable[[], bool]


def flock(lock_path: Path, *, block: bool) -> ContextManager[LockFile]:
    @contextmanager
    def impl() -> Iterator[LockFile]:
        with open(lock_path, 'w+') as lock_file:

            def is_locked() -> bool:
                return not lock_file.closed

            def is_not_locked() -> bool:
                return False

            try:
                block_op = 0 if block else fcntl.LOCK_NB
                fcntl.flock(lock_file, fcntl.LOCK_EX | block_op)
                yield LockFile(path=lock_path, is_locked=is_locked)

            except BlockingIOError:
                # `flock` is intended to be used at the head of a `with` block.
                # Therefore, if we propagate the exception, the caller will be
                # unable to tell whether the exception was raised by the `flock`
                # call or by the body of the `with` block, unless they also
                # wrap the body in an exception handler. It's more convenient
                # to have the context manager return a value we can test.
                yield LockFile(path=lock_path, is_locked=is_not_locked)

    return impl()


def file_lock(path: Path, *, block: bool) -> ContextManager[LockFile]:
    assert path.name, 'file_lock: empty basename: {path}'
    assert path.parent.is_dir(), 'file_lock: parent does not exist: {path}'
    return flock(path.parent / f'{path.name}.lock', block=block)


def dir_lock(path: Path, *, block: bool) -> ContextManager[LockFile]:
    assert path.is_dir(), 'dir_lock: not a directory'
    return flock(path / '.lock', block=block)


class LockedJson(Protocol):
    def get_data(self, default: T, get: Callable[[Any], T]) -> T:
        ...

    def put_data(self, data: Any) -> None:
        ...


def json_file_lock(path: Path) -> ContextManager[LockedJson]:

    @contextmanager
    def impl() -> Iterator[LockedJson]:

        with file_lock(path, block=True) as lock:
            assert lock.is_locked(), f'json_file_lock: failed to lock: {path}'
            tmp_path = path.parent / f'{path.name}.tmp'

            class LockedJsonImpl(NamedTuple):

                def get_data(self, default: T, get: Callable[[Any], T]) -> T:
                    assert lock.is_locked(), f'json_file_lock: get_data without a lock: {path}'
                    try:
                        with open(path, 'r') as json_file:
                            return get(json.load(json_file))
                    except FileNotFoundError:
                        return default

                def put_data(self, data: Any) -> None:
                    assert lock.is_locked(), f'json_file_lock: put_data without a lock: {path}'
                    with open(tmp_path, 'w') as tmp_file:
                        json.dump(data, tmp_file, separators=(',', ':'))
                    shutil.move(tmp_path, path)

            yield LockedJsonImpl()

    return impl()


def iter_non_empty(iter: Iterable[T]) -> bool:
    return any(True for i in iter)


def sets_disjoint(*sets: set[T]) -> bool:
    return all(sets[i].isdisjoint(sets[j])
               for i in range(len(sets))
               for j in range(i + 1, len(sets)))


# A CpuSet represents a collection of computational resources
# that may be available for running tasks. A "CPU" is represented
# by a lock file which is held while a task is being performed.
class CpuSet(NamedTuple):
    # The number of CPUs we have lock files for.
    present: int
    # The format string to translate CPU number to lock directory name.
    fmt: str
    # The path containing lock directories.
    path: Path

    def cpu_name(self, cpu_id) -> str:
        assert 0 <= cpu_id < self.present, f'cpu_name: invalid cpu_id: {cpu_id}'
        return f'{cpu_id:{self.fmt}}'

    # The directory containing the lock file.
    def cpu_dir(self, cpu_id) -> Path:
        return self.path / self.cpu_name(cpu_id)

    def set(self) -> set[int]:
        return set(range(self.present))


# We need a lock per CPU, so we can wait on CPU availability.
# We create lock directories up to the allowed number of CPUs.
# We don't remove existing directories exceeding the allowance,
# since other runners may be using them.
# This should only be used when we have a lock on cpus_allowed.txt.
def build_cpu_set(cpus_path: Path, cpus_allowed: int) -> CpuSet:
    cpus_path.mkdir(parents=True, exist_ok=True)

    existing_cpus = list(enumerate(sorted(os.listdir(cpus_path))))
    cpus_present = max(cpus_allowed, len(existing_cpus))

    cpu_digits = len(str(cpus_present - 1))
    cpu_fmt = f'0{cpu_digits}d'

    assert all((cpus_path / j).is_dir() for i, j in existing_cpus), \
        'initialise_cpus error: cpus entries are not all directories'

    assert all(j.isdigit() and i == int(j) for i, j in existing_cpus), \
        'initialise_cpus error: cpu lock directories have unexpected names'

    cpu_set = CpuSet(present=cpus_present, fmt=cpu_fmt, path=cpus_path)

    for cpu_num, existing_cpu in existing_cpus:
        new_cpu_name = f'{cpu_num:{cpu_fmt}}'
        if new_cpu_name != existing_cpu:
            assert int(new_cpu_name) == int(existing_cpu)
            new_cpu_path = cpus_path / new_cpu_name
            assert not new_cpu_path.exists()
            # It's ok for us to rename these, since we are the only runner
            # allowed to allocate CPUs to new tasks, and we preserve numbers.
            os.rename(cpus_path / existing_cpu, new_cpu_path)

    for cpu_num in range(len(existing_cpus), cpus_allowed):
        cpu_set.cpu_dir(cpu_num).mkdir()

    return cpu_set


class ActiveRunnerStatus(NamedTuple):
    is_active: bool
    is_cache_valid: bool


@dataclass(kw_only=True)
class RunnerState:
    cond_var: threading.Condition

    tasks_running: set[TaskRun]
    runners_waiting: set[str]

    cpu_set: CpuSet
    cpus_allowed: int
    cpus_waiting: set[int]
    cpus_working: set[int]
    cpus_idle: set[int]


def default_priority(task: Task) -> int:
    return 200


targets_admitted: set[str] = {
    'RISCV64-O1',
    'RISCV64-MCS-O1',
}

functions_rejected: dict[str, set[str]] = {
    'RISCV64-O1': {
        'create_untypeds_for_region',
    },
    'RISCV64-MCS-O1': {
        'create_untypeds_for_region',
    },
}


# Enumerate the tasks for a job.
# Used to populate the tasks table in the database when starting a job.
def get_tasks_for_job(jobs_path: Path,
                      priority: EnqueuePriority = default_priority) -> GetTasksForJob:

    def get_tasks(job_id: str) -> Sequence[EnqueueTask]:
        job_path = jobs_path / job_id

        enqueue_tasks: list[EnqueueTask] = []
        targets: list[str] = []

        for target in os.listdir(job_path / 'targets'):
            if target not in targets_admitted:
                continue

            target_path = job_path / 'targets' / target
            functions_list_path = target_path / 'target' / 'functions-list.txt'
            if not functions_list_path.is_file():
                continue
            targets.append(target)

            def enq_task(function: str) -> EnqueueTask:
                task = Task(job_id=job_id, target=target, function=function)
                return EnqueueTask(task=task, priority=priority(task))

            with open(functions_list_path) as functions_list:
                enqueue_tasks.extend(enq_task(function)
                                     for function in (line.strip() for line in functions_list)
                                     if function not in functions_rejected.get(target, set()))

        return enqueue_tasks

    return get_tasks


result_re = re.compile(
    r'Result (?P<result>\w+) for pair Pairing \((?P<name>\w+) \(ASM\) <= \S+ \(C\)\), time taken: .*')
underspecified_fn_re = re.compile(
    r'Aborting Problem \(Pairing \((?P<name>\S+) \(ASM\) <= \S+ \(C\)\)\): underspecified \S+')
complex_loop_re = re.compile(
    r'Aborting Problem \(Pairing \((?P<name>\S+) \(ASM\) <= \S+ \(C\)\)\), complex loop')
impossible_re = re.compile(
    r"Possibilities for '(?P<name>\S+)': \[\]")
split_limit_assertion_re = re.compile(
    r"assert not 'split limit found'")


def graph_refine_result(name: str, report_path: Path) -> TaskResult:
    if report_path.is_file():
        with open(report_path) as report:
            for line in report:
                line = line.strip()

                match = result_re.fullmatch(line)
                if match:
                    assert match['name'] == name
                    if match['result'] == 'True':
                        return TaskResult.PASSED
                    if match['result'] == 'False':
                        return TaskResult.FAILED
                    if match['result'] == 'ProofNoSplit':
                        return TaskResult.NO_SPLIT
                    if match['result'] == 'ProofEXCEPT':
                        return TaskResult.EXCEPT
                    else:
                        return TaskResult.MALFORMED

                match = underspecified_fn_re.fullmatch(line)
                if match:
                    assert match['name'] == name
                    return TaskResult.UNDERSPECIFIED

                match = complex_loop_re.fullmatch(line)
                if match:
                    assert match['name'] == name
                    return TaskResult.COMPLEX_LOOP

    return TaskResult.NO_RESULT


def graph_refine_impossible(name: str, log_path: Path) -> bool:
    if log_path.is_file():
        with open(log_path) as log:
            for line in log:
                line = line.strip()
                match = impossible_re.fullmatch(line)
                if match:
                    assert match['name'] == name
                    return True
    return False


def split_limit_assertion(log_path: Path) -> bool:
    if log_path.is_file():
        with open(log_path) as log:
            for line in log:
                line = line.strip()
                if line == "assert not 'split limit found'":
                    return True
    return False


def ensure_dict(data: Any) -> dict[str, Any]:
    assert isinstance(data, dict)
    assert all(isinstance(k, str) for k in data)
    return data


class Runner(NamedTuple):
    work_dir: Path
    runner_id: str
    instance_id: str
    graph_refine: Path

    def jobs_db(self) -> ContextManager[JobsDB]:
        @contextmanager
        def impl() -> Iterator[JobsDB]:
            conn = sqlite3.connect(self.work_dir / 'private' / 'jobs.db')
            try:
                conn.row_factory = sqlite3.Row
                yield JobsDB(conn=conn, get_tasks=get_tasks_for_job(jobs_path=self.jobs_dir()))
            finally:
                conn.close()

        return impl()

    def jobs_dir(self) -> Path:
        return self.work_dir / 'public' / 'jobs'

    def targets_dir(self, job_id: str) -> Path:
        return self.jobs_dir() / job_id / 'targets'

    def runner_lock_dir(self, runner_id: str) -> Path:
        return self.work_dir / 'private' / 'runners' / runner_id

    def runner_lock(self, runner_id: str, *, block: bool) -> ContextManager[LockFile]:
        return dir_lock(self.runner_lock_dir(runner_id), block=block)

    def new_jobs(self) -> Sequence[WaitingJob]:
        new_dir = self.work_dir / 'private' / 'new'
        if not new_dir.is_dir():
            return []

        def get_job(entry: os.DirEntry) -> Iterator[WaitingJob]:
            job_id = entry.name
            job_path = new_dir / job_id
            if job_path.is_file():
                with open(job_path) as job_file:
                    time_job_submitted = job_file.read().strip()
                yield WaitingJob(job_id=job_id, time_job_submitted=time_job_submitted)

        return [job for entry in os.scandir(new_dir) for job in get_job(entry)]

    def add_new_jobs(self) -> None:
        new_jobs = self.new_jobs()
        with self.jobs_db() as db:
            db.add_waiting_jobs(new_jobs)
        for job in new_jobs:
            write_log(f'add_new_jobs: added job {job.job_id}')
            (self.work_dir / 'private' / 'new' / job.job_id).unlink()

    # Get the allowed number of CPUs, and hold a lock on cpus_allowed.txt.
    def cpus_allowed_lock(self) -> ContextManager[int]:
        cpus_allowed_path = self.work_dir / 'private' / 'cpus_allowed.txt'

        @contextmanager
        def impl() -> Iterator[int]:
            with file_lock(cpus_allowed_path, block=True) as lock:
                assert lock.is_locked(), 'cpus_allowed_lock: failed to lock cpus_allowed.txt'

                # Let it crash if the file doesn't exist, or has invalid contents.
                with open(cpus_allowed_path) as cpus_allowed_file:
                    cpus_allowed = int(cpus_allowed_file.read().strip())

                yield cpus_allowed

        return impl()

    # Take a lock on the active_runner_id.txt file, and return flags indicating:
    # - whether our runner_id is the active runner ID,
    # - if so, whether the most recently set instance ID matches ours.
    # The latter is used to determine cache validity.
    def active_runner_lock(self) -> ContextManager[ActiveRunnerStatus]:
        runner_id_path = self.work_dir / 'private' / 'active_runner_id.txt'
        instance_id_path = self.work_dir / 'private' / 'active_instance.txt'

        @contextmanager
        def impl() -> Iterator[ActiveRunnerStatus]:
            with file_lock(runner_id_path, block=True) as lock:
                assert lock.is_locked(), f'active_runner_lock: failed to acquire lock'

                try:
                    with open(runner_id_path, 'r') as runner_id_file:
                        is_active = runner_id_file.read().strip() == self.runner_id
                except FileNotFoundError:
                    is_active = False

                if not is_active:
                    yield ActiveRunnerStatus(is_active=False, is_cache_valid=False)
                    return

                try:
                    with open(instance_id_path, 'r') as instance_id_file:
                        is_cache_valid = instance_id_file.read().strip() == self.instance_id
                except FileNotFoundError:
                    is_cache_valid = False

                yield ActiveRunnerStatus(is_active=True, is_cache_valid=is_cache_valid)

        return impl()

    # Invalidates caches of any other runners.
    # This should only be called when we have locks on both:
    # - our runner_id directory,
    # - the active_runner_id.txt file.
    def set_active_instance_id(self) -> None:
        with open(self.work_dir / 'private' / 'active_instance.txt', 'w') as instance_id_file:
            print(self.instance_id, file=instance_id_file)

    def other_runners(self) -> set[str]:
        return set(r for r in os.listdir(self.work_dir / 'private' / 'runners')
                   if r != self.runner_id)

    def wait_for_runners(self, runners: Iterable[str], state: RunnerState) -> None:
        for runner in runners:
            write_log(f'wait_for_runners: waiting for {runner}')
            state.runners_waiting.add(runner)

            def thread_fn(runner: str) -> None:
                with self.runner_lock(runner, block=True) as lock:
                    assert lock.is_locked(), f'wait_for_runners: failed to lock runner {runner}'
                    with state.cond_var:
                        write_log(f'wait_for_runners: got {runner}')
                        state.runners_waiting.remove(runner)
                        # Only the active runner should archive another runner.
                        with self.active_runner_lock() as active_runner:
                            if active_runner.is_active:
                                with self.jobs_db() as db:
                                    db.unassign_tasks(runner)
                                shutil.rmtree(self.runner_lock_dir(runner))
                        state.cond_var.notify()

            thread = threading.Thread(target=thread_fn, args=(runner, ), daemon=True)
            thread.start()

    def cpus_dir(self) -> Path:
        return self.work_dir / 'private' / 'cpus'

    # Called from the main thread while holding the active_runner_id lock
    # and the shared state condition variable.
    # Initially adds each CPU to `cpus_waiting`, and starts a thread to wait
    # for the CPU lock. When the thread acquires the lock, it moves the CPU to
    # `cpus_idle`, and notifies the main thread.
    def wait_for_cpus(self, cpus: Iterable[int], state: RunnerState) -> None:
        for cpu in cpus:
            write_log(f'wait_for_cpus: waiting for CPU {state.cpu_set.cpu_name(cpu)}')
            state.cpus_waiting.add(cpu)

            def thread_fn(cpu: int) -> None:
                with dir_lock(state.cpu_set.cpu_dir(cpu), block=True) as lock:
                    assert lock.is_locked(), f'wait_for_cpus: failed to lock CPU {cpu}'
                with state.cond_var:
                    write_log(f'wait_for_cpus: got CPU {state.cpu_set.cpu_name(cpu)}')
                    state.cpus_waiting.remove(cpu)
                    state.cpus_idle.add(cpu)
                    state.cond_var.notify()

            thread = threading.Thread(target=thread_fn, args=(cpu, ), daemon=True)
            thread.start()

    def initialise_state(self, cond_var: threading.Condition) -> Optional[RunnerState]:
        with self.active_runner_lock() as active_runner:
            if not active_runner.is_active:
                return None

            with self.cpus_allowed_lock() as cpus_allowed:
                cpu_set = build_cpu_set(self.cpus_dir(), cpus_allowed)

            state = RunnerState(cond_var=cond_var,
                                tasks_running=set(),
                                runners_waiting=set(),
                                cpu_set=cpu_set,
                                cpus_allowed=cpus_allowed,
                                cpus_waiting=set(),
                                cpus_working=set(),
                                cpus_idle=set())

            self.wait_for_cpus(cpu_set.set(), state)
            self.wait_for_runners(self.other_runners(), state)

            with self.jobs_db() as db:
                db.initialise()
                # In case we are recovering from a crash/reboot.
                db.unassign_tasks(self.runner_id)

            self.add_new_jobs()

            self.set_active_instance_id()
            return state

    # Assumes we have the runner_id lock, and the active_runner_id lock.
    def refresh_state(self, state: RunnerState, is_cache_valid: bool) -> None:
        if is_cache_valid:
            write_log('refresh_state: cache is valid, minimally refreshing CPU set')
            with self.cpus_allowed_lock() as cpus_allowed:
                if state.cpus_allowed < cpus_allowed:
                    state.cpu_set = build_cpu_set(self.cpus_dir(), cpus_allowed)
                    # Force generation of `new_cpus` before calling `wait_for_cpus`,
                    # because`wait_for_cpus` can modify `cpus_waiting` and `cpus_idle`.
                    new_cpus = state.cpu_set.set() \
                        - state.cpus_working - state.cpus_waiting - state.cpus_idle
                    self.wait_for_cpus(new_cpus, state)
                state.cpus_allowed = cpus_allowed
        else:
            write_log('refresh_state: cache is not valid, refreshing everything')
            with self.cpus_allowed_lock() as cpus_allowed:
                state.cpu_set = build_cpu_set(self.cpus_dir(), cpus_allowed)
                # CPUs we thought were idle may have become occupied,
                # so we need to wait for them again.
                state.cpus_idle.clear()
                # Force generation of `wait_cpus` before calling `wait_for_cpus`,
                # because`wait_for_cpus` can modify `cpus_waiting` and `cpus_idle`.
                wait_cpus = state.cpu_set.set() - state.cpus_working - state.cpus_waiting
                self.wait_for_cpus(wait_cpus, state)
                state.cpus_allowed = cpus_allowed
            runners = self.other_runners() - state.runners_waiting
            self.wait_for_runners(runners, state)
            self.set_active_instance_id()

    def run_graph_refine(self, task: TaskRun, state: RunnerState) -> None:
        if task in state.tasks_running:
            return

        cpu = state.cpus_idle.pop()
        state.cpus_working.add(cpu)

        log_info = f'{task.function} {task.target} {task.job_id} {task.run_id}'
        write_log(f'run_graph_refine: begin {log_info}')

        smt_dir = self.jobs_dir() / task.job_id / 'smt'
        target_path = self.jobs_dir() / task.job_id / 'targets' / task.target
        target_inputs = target_path / 'target'
        task_dir = target_path / 'functions' / task.function / task.run_id
        report_path = task_dir / 'report.txt'
        log_path = task_dir / 'log.txt'

        l4v_arch: Optional[str] = None
        with open(target_inputs / 'config.env') as config_env:
            for line in config_env:
                var, val = line.strip().split('=', maxsplit=1)
                if var == "L4V_ARCH":
                    l4v_arch = val

        assert l4v_arch is not None

        for new_dir in [smt_dir, task_dir]:
            new_dir.mkdir(parents=True, exist_ok=True)

        # Runs in the thread started below.
        def thread_finished(proc_result: Optional[int]) -> None:
            result = graph_refine_result(task.function, report_path)

            if result is TaskResult.EXCEPT:
                if split_limit_assertion(log_path):
                    result = TaskResult.NO_SPLIT

            elif result is TaskResult.NO_RESULT:
                if graph_refine_impossible(task.function, log_path):
                    result = TaskResult.IMPOSSIBLE
                elif proc_result is None:
                    result = TaskResult.TIMEOUT
                elif proc_result < 0:
                    result = TaskResult.KILLED

            with open(task_dir / 'exit_code.txt', 'w') as exit_code_txt:
                print(proc_result, file=exit_code_txt)

            write_log(f'run_graph_refine: result {result.name} {log_info}')

            with state.cond_var:
                state.tasks_running.remove(task)
                state.cpus_working.remove(cpu)
                state.cpus_idle.add(cpu)

                with self.jobs_db() as db:
                    db.finish_run(runner_id=self.runner_id, task=task, result=result)

                state.cond_var.notify()

        class StartOk(NamedTuple):
            proc: subprocess.Popen

        class StartExcept(NamedTuple):
            ex: Exception

        subproc_queue: queue.Queue[StartOk | StartExcept] = queue.Queue()

        def thread_fn() -> None:
            try:
                cmd: list[str | Path] = \
                    [self.graph_refine, target_inputs, f'trace-to:{report_path}', task.function]

                assert l4v_arch is not None
                env: dict[str, str | Path] = \
                    {**os.environ, "L4V_ARCH": l4v_arch, "GRAPH_REFINE_SMT2_DIR": smt_dir}

                with dir_lock(state.cpu_set.cpu_dir(cpu), block=True):
                    with open(log_path, 'w') as log_file:
                        proc = subprocess.Popen(cmd, cwd=task_dir, env=env,
                                                stdin=subprocess.DEVNULL, stdout=log_file,
                                                stderr=subprocess.STDOUT)

                    subproc_queue.put(StartOk(proc))

                    try:
                        result: Optional[int] = proc.wait(timeout=259200)
                    except subprocess.TimeoutExpired:
                        result = None
                    finally:
                        try:
                            os.killpg(proc.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                        finally:
                            thread_finished(result)

            except Exception as ex:
                subproc_queue.put(StartExcept(ex))
                raise

        thread = threading.Thread(target=thread_fn)
        thread.start()

        thread_start_result = subproc_queue.get()
        if isinstance(thread_start_result, StartExcept):
            raise thread_start_result.ex

        state.tasks_running.add(task)

    def start_tasks(self, state: RunnerState) -> None:
        assert sets_disjoint(state.cpus_waiting, state.cpus_working, state.cpus_idle), \
            'start_tasks: CPU sets not disjoint'
        assert state.cpu_set.set() == state.cpus_waiting | state.cpus_working | state.cpus_idle, \
            'start_tasks: CPU sets incomplete'
        assert state.cpus_allowed <= state.cpu_set.present, \
            'start_tasks: allowed CPUs not present'
        cpus_busy = len(state.cpus_waiting) + len(state.cpus_working)
        cpus_available = state.cpus_allowed - cpus_busy
        if cpus_available <= 0:
            return
        write_log(f'start_tasks: {cpus_available} CPUs available')
        with self.jobs_db() as db:
            tasks = db.assign_tasks(self.runner_id, cpus_available)
        for task in tasks:
            self.run_graph_refine(task, state)

    def export_json_tasks(self, dirty_tasks: DirtyTasks) -> None:
        for job_id, dirty_targets in dirty_tasks.items():
            for target, dirty_functions in dirty_targets.items():
                functions_json_path = self.targets_dir(job_id) / target / 'functions.json'
                with json_file_lock(functions_json_path) as functions_json:
                    functions = ensure_dict(functions_json.get_data({}, lambda fs: fs))
                    for function, task_data in dirty_functions.items():
                        function_data = ensure_dict(functions.setdefault(function, {}))
                        if isinstance(task_data.assignment, TaskUnassigned):
                            function_data['assignment'] = None
                        elif isinstance(task_data.assignment, TaskAssigned):
                            function_data['assignment'] = task_data.assignment._asdict()
                        runs = ensure_dict(function_data.setdefault('runs', {}))
                        for assignment, run_data in task_data.runs.items():
                            runner = ensure_dict(runs.setdefault(assignment.runner_id, {}))
                            runner[assignment.run_id] = run_data._asdict()
                    functions_json.put_data(functions)

    def export_json_jobs(self, *, dirty_jobs: DirtyJobs, dirty_targets: DirtyTargets) -> None:
        # Maps from job_id to time submitted.
        dirty_waiting: dict[str, str] = {}
        dirty_running: dict[str, str] = {}
        dirty_finished: dict[str, str] = {}

        for job_id, job_data in dirty_jobs.items():
            job_status = {"timestamps": job_data._asdict(),
                          "targets": dirty_targets.get(job_id, {})}

            with json_file_lock(self.jobs_dir() / job_id / 'job_status.json') as job_status_json:
                job_status_json.put_data(job_status)

            dirty_set = dirty_finished if job_data.time_job_finished is not None \
                else dirty_running if job_data.time_job_started is not None \
                else dirty_waiting

            dirty_set[job_id] = job_data.time_job_submitted

        with json_file_lock(self.work_dir / 'public' / 'jobs.json') as jobs_json:
            jobs = ensure_dict(jobs_json.get_data({}, lambda js: js))

            class ListedJob(NamedTuple):
                job_id: str
                submitted: str

            def time_job_submitted_key(job: ListedJob) -> str:
                return job.submitted

            def ensure_job(job_data: Any) -> ListedJob:
                assert isinstance(job_data, dict)
                assert isinstance(job_data["job_id"], str)
                assert isinstance(job_data["submitted"], str)
                return ListedJob(**job_data)

            def ensure_jobs(jobs_data: Any) -> list[ListedJob]:
                assert isinstance(jobs_data, list)
                return [ensure_job(job) for job in jobs_data]

            def build_jobs(key: str, new: dict[str, str], exclude: Sequence[dict[str, str]],
                           limit: Optional[int] = None) -> list[dict[str, str]]:

                jobs_list = [j for j in ensure_jobs(jobs.get(key, []))
                             if j.job_id not in new and not any(j.job_id in e for e in exclude)]

                jobs_list.extend(ListedJob(job_id, submitted) for job_id, submitted in new.items())
                jobs_list.sort(key=time_job_submitted_key, reverse=True)

                if limit is not None:
                    jobs_list = jobs_list[:limit]

                return [job._asdict() for job in jobs_list]

            waiting = build_jobs(key='waiting', new=dirty_waiting,
                                 exclude=(dirty_running, dirty_finished))
            running = build_jobs(key='running', new=dirty_running,
                                 exclude=(dirty_waiting, dirty_finished))
            finished = build_jobs(key='finished', new=dirty_finished,
                                  exclude=(dirty_waiting, dirty_running), limit=500)

            jobs_json.put_data({"waiting": waiting, "running": running, "finished": finished})

    def export_json(self, state: RunnerState) -> None:
        with self.jobs_db() as db, db.export_dirty_state() as dirty_state:
            self.export_json_tasks(dirty_state.tasks)
            self.export_json_jobs(dirty_jobs=dirty_state.jobs, dirty_targets=dirty_state.targets)
            dirty_state.clean()

    # Assumes we are holding our runner_id lock.
    def do_work(self) -> None:
        # We use a condition variable to allow the main thread to receive
        # notifications from other threads, while also controlling access
        # to shared resources. To ensure the main thread doesn't miss any
        # notifications, it must always be holding the condition variable,
        # except when it pauses to wait for notifications.
        cond_var = threading.Condition()
        with cond_var:
            state = self.initialise_state(cond_var)

            if state is None:
                return

            while True:
                with self.active_runner_lock() as active_runner:

                    if active_runner.is_active:
                        write_log('do_work: acquired active runner lock')
                        self.refresh_state(state, active_runner.is_cache_valid)
                        self.add_new_jobs()
                        self.start_tasks(state)
                        self.export_json(state)
                    else:
                        write_log('do_work: not the active runner')

                    if not state.tasks_running:
                        if not active_runner.is_active:
                            write_log('do_work: no running tasks, exiting')
                            return
                        if not state.runners_waiting and not state.cpus_waiting:
                            write_log('do_work: not waiting on CPUs or runners, exiting')
                            return
                        write_log('do_work: no tasks, but waiting on'
                                  + f' {len(state.cpus_waiting)} CPUs and'
                                  + f' {len(state.runners_waiting)} runners')
                    else:
                        write_log(f'do_work: {len(state.tasks_running)} tasks still running')

                # A long timeout is ok, since cond_var will be notified by
                # other threads as soon as there is a finished task or idle CPU.
                # The timeout limits how long it takes us to:
                # - Start using an increased CPU allowance.
                # - Add new jobs to the database and its exported JSON.
                write_log('do_work: waiting for events')
                cond_var.wait(timeout=50)

    def have_new_jobs(self) -> bool:
        with self.active_runner_lock() as active_runner:
            return active_runner.is_active and iter_non_empty(self.new_jobs())

    def run(self) -> None:
        self.runner_lock_dir(self.runner_id).mkdir(parents=True, exist_ok=True)

        # The outer loop here avoids a race condition during shutdown.
        # Most runners will only iterate the outer loop once, since `do_work` should
        # normally continue until the runner's work is exhausted.

        while True:
            with self.runner_lock(self.runner_id, block=False) as lock:
                if not lock.is_locked():
                    write_log('run: failed to acquire runner lock, exiting')
                    return

                # We are the runner authorised to use our runner_id,
                # so we need to do the work.
                write_log('run: acquired runner lock')
                self.do_work()

            # If `do_work` returned, then it has completed all the work it could see.
            # Normally, that means we want to shut down.

            # However, there is a potential race with new job submissions.

            # After submitting a new job, the submitter will attempt to start a new
            # runner. The new runner will exit immediately if there is already a
            # runner holding runner_lock (see above). If the existing runner
            # has already decided to shut down, but has not yet released runner_lock,
            # then we could be left without a runner for the new job.

            # To avoid the race, ensuring that we're left with exactly one runner for
            # the new job, the existing runner (but not the new runner) must perform an
            # additional check for new work after it has released runner_lock.

            write_log('run: released runner lock, checking for new jobs')
            if not self.have_new_jobs():
                write_log('run: no new jobs, exiting')
                return


# Use a low-level redirect to make sure we get everything.
def redirect_to_log(path: Path) -> None:
    sys.stdout.flush()
    sys.stderr.flush()
    log_fd = os.open(path, os.O_WRONLY | os.O_CREAT)
    os.set_inheritable(log_fd, True)
    os.dup2(log_fd, 1)
    os.dup2(log_fd, 2)
    os.close(log_fd)


class RunnerConfig(NamedTuple):
    work_dir: Path
    runner_id: str
    graph_refine: Path

    def run(self) -> None:
        runner = Runner(work_dir=self.work_dir,
                        runner_id=self.runner_id,
                        instance_id=mk_unique_id(),
                        graph_refine=self.graph_refine)

        log_dir = self.work_dir / 'public' / 'runners' / self.runner_id / 'logs'
        log_dir.mkdir(parents=True, exist_ok=True)

        redirect_to_log(log_dir / f'{runner.instance_id}.log')
        runner.run()


runner_id_re = re.compile(r'\w+')


def parse_args() -> RunnerConfig:
    def runner_id(arg: str) -> str:
        if runner_id_re.fullmatch(arg):
            return arg
        raise argparse.ArgumentTypeError(f'{arg} is not a valid runner ID')

    def work_dir_path(arg: str) -> Path:
        if os.path.isdir(arg) and os.access(arg, os.R_OK | os.W_OK | os.X_OK):
            return Path(arg).resolve()
        raise argparse.ArgumentTypeError(f'{arg} is not a valid work directory')

    def graph_refine_script(arg: str) -> Path:
        if os.path.isfile(arg) and os.access(arg, os.R_OK | os.X_OK):
            return Path(arg).resolve()
        raise argparse.ArgumentTypeError(f'{arg} is not a valid work directory')

    parser = argparse.ArgumentParser(description='Run graph-refine jobs')
    parser.add_argument('--id', metavar='ID', required=True, type=runner_id,
                        help='Runner ID')
    parser.add_argument('--work', metavar='DIR', required=True, type=work_dir_path,
                        help='Root of the graph-refine work directory')
    parser.add_argument('--graph-refine-py', metavar='PATH', type=graph_refine_script,
                        default=os.environ.get('GRAPH_REFINE_SCRIPT'),
                        help='Path to graph-refine script')

    parser.set_defaults(redirect_output=False)
    args = parser.parse_args()

    return RunnerConfig(work_dir=args.work,
                        runner_id=args.id,
                        graph_refine=args.graph_refine_py)


def main(runner_config: RunnerConfig) -> int:
    runner_config.run()
    return 0


if __name__ == '__main__':
    exit(main(parse_args()))
