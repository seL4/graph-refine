# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause


# You must have the typing module in your Python2.7 search path.
# Use `pip2.7 install typing` to install the module.
from typing import (Any, Dict, IO, Iterable, List, NamedTuple, Optional, Protocol, Tuple, Union)

# will change to collections.abc in Python3+
from collections import MutableMapping

import copy
import os
import signal
import subprocess
import inspect

# Common types:
# The types defined below are left unspecified in this module. This allows
# us to interface with the untyped, "legacy" parts of graph-refine without
# having said parts as dependencies. Thus, the untyped parts can import
# the typed parts without introducing circular dependencies.

Hypothesis = Any
SMTExpr = Any
VariableEnvironment = Any
FetchModelResponseVerdict = Any

SExpr_rec = Any
SExpr = Union[str, Tuple[SExpr_rec, ...]]  # mypy lacks support for rec. types
# SExpr.__doc__ = """An S-expression representation which represents atoms as
# strings and cons cells as tuples. `SExpr_rec` will be eliminated once `mypy`
# gets support for recursive types."""


CheckModelIterationState = NamedTuple('CheckModelIterationState',
                                      [('confirmed_hypotheses', List[Hypothesis]),
                                       ('test_hypotheses', List[Hypothesis]),
                                       ('candidate_model', 'Optional[PersistableModel]'),
                                       ('remaining_solvers', 'List[SolverImpl]')])
# CheckModelIterationState.__doc__ = """An immutable data class containing the
# saved state of a suspended bogus model check (cf. `check_model_iteration` in
# the `SolverContextProtocol` class)."""

CMIAbort = NamedTuple('CMIAbort', [])
CMIResult = NamedTuple('CMIResult', [('candidate_model', 'PersistableModel')])
CMIContinue = NamedTuple('CMIContinue',
                         [('next_solver', 'SolverImpl'),
                          ('next_hypotheses', List[Hypothesis]),
                          ('state', CheckModelIterationState)])
CheckModelIterationVerdict = Union[CMIAbort, CMIResult, CMIContinue]
# CheckModelIterationVerdict.__doc__ = """A verdict on whether a model passes
# the bogus model check, and if not, whether to continue to subject it to the
# model repair process (cf. `check_model_iteration` below)."""


class SolverContextProtocol(Protocol):
    """The protocol implemented by solver contexts such as `solver.Solver`.

    A solver context (not to be confused with a solver implementation (cf.
    `SolverImpl`) stores essential state and methods required to communicate
    with the various SMT solvers. This includes the current pvalids, the
    current stack equations, the current model variables and so on.

    The class implementing a solver context (`solver.Solver`) currently lies
    in the non-type-checked 'legacy' part of `graph-refine`. However, some
    classes in the typed part rely on methods exposed by the solver context.
    The `SolverContextProtocol` serves to decouple these classes from the
    solver context implementation, averting a circular dependency.
    """

    def smt_expr(self, expr, env):
        # type: (Any, Any) -> Any
        """Returns a string representation (ready to be passed to an SMT solver) of the given S-expression.

        Args:
            expr: The given expression.
            env: The variable substitution environment.
        """
        raise NotImplementedError

    def get_strategy(self):
        # type: () -> Iterable[Tuple[SolverImpl,str]]
        """Returns the collection of available SMT solvers, associated with their supported strategies (hyp/all)."""
        raise NotImplementedError

    def fetch_model_request(self):
        # type: () -> SMTExpr
        """Returns the SMT input message for retrieving a (counter)model from an SMT solver."""
        raise NotImplementedError

    def fetch_model_response(self, model, stream=None, recursion=False):
        # type: (PersistableModel, Optional[IO[str]], bool) -> Optional[FetchModelResponseVerdict]
        """Updates the given model based on the SMT output message read from the given stream.

        The given stream should contain an SMT output message that is
        compatible with the variables of the solver context (e.g. one emitted
        in response to the input message given by `fetch_model_request`.

        Args:
            model: The given model (which is to be updated).
            stream: The given IO stream (from which the message will be read).
            recursion: True if recursion is enabled.
        """
        raise NotImplementedError

    def check_model_iteration(self, hyps, state, (res, model)):
        # type: (List[SMTExpr], Optional[CheckModelIterationState], Tuple[str, PersistableModel]) -> CheckModelIterationVerdict
        """Performs the check for incomplete models and returns a verdict on whether to continue with the model repair process.

        When an SMT solver refutes a hypothesis posited by `graph-refine`,
        it provides a countermodel, a variable assignment which makes the
        hypothesis false. Unfortunately, these returned models may be
        bogus/incomplete. Such incomplete models can be repaired using one
        or more iterations of a 'model repair' procedure. This method
        checks if the given model is bogus, and provides a verdict on whether
        to attempt the model repair procedure.

        After an iteration of the model repair procedure, the check has to be
        performed again, continuing from a saved `CheckModelIterationState`.

        Args:
            hyps: The original hypotheses tested by the refuted query (not the subsequent model repair query!).
            state: The given saved state (if continuing) or None.
            (res, model): The response (un/sat) of the latest query, along with the corresponding counter-model (if present).
        """
        raise NotImplementedError

    def exec_slow_solver(self, input_msgs, timeout, solver):
        # type: (List[SMTExpr], int, SolverImpl) -> OfflineSolverExecution
        """Starts the execution of the given offline SMT solver with the given input messages.

        Args:
            input_msgs: The given input messages (to send to the solver).
            timeout: The maximum time allotted to the query (in ms).
            solver: The given SMT solver implementation.
        """
        raise NotImplementedError


class SolverImpl:
    """Stores data about an executable SMT solver implementation.

    A `SolverImpl` object represents an SMT solver implementation, i.e. an
    executable program that supports the SMTLIB2 input/output format, alongside
    supporting information required to send SMT queries to the solver. These
    attributes are configured in a solverlist file (see the doc. in `solver`).

    Attributes:
        name: the human-readable name of the solver, as given in the solverlist.
        fast: True if the solver is online, False otherwise.
        args: location of the executable, along with command-line arguments.
        timeout: The maximum time allotted to the solver (in a single query, ms).
    """
    def __init__(self, name, fast, args, timeout):
        # type: (str, bool, List[str], int) -> None
        self.fast = fast
        self.args = args
        self.timeout = timeout
        self.origname = name
        self.mem_mode = None  # type: Optional[str] # ('8','32','64',None)
        if self.fast:
            self.name = name + ' (online)'
        else:
            self.name = name + ' (offline)'

    def __repr__(self):
        return 'SolverImpl(%r, %r, %r, %r, %r)' % (self.name,
                                                   self.fast,
                                                   self.mem_mode,
                                                   self.args,
                                                   self.timeout)


class OfflineSolverExecution:
    """Stores the state of a currently executing offline SMT solver query process.

    An `OfflineSolverExecution` instance is created each time we execute an SMT
    query using an offline solver (as configured in a solverlist). The instance
    encapsualtes the state of the running process, stores the name of the
    associated solver script (SMT input) file, and provides convenience methods
    for manipulating these.

    Attributes:
        solver: The solver implementation handling the current query.
        process: The running process encapsulated by the object instance.
        stdout: The output stream of the encapsulated process.
        filename: The name of the file containing the current query.
    """
    def __init__(self, solver, process, filename):
        # type: (SolverImpl, subprocess.Popen[str], str) -> None
        self.solver = solver
        self.process = process
        assert process.stdout is not None
        self.stdout = process.stdout  # type: IO[str]
        self.filename = filename
        self.dead = False

    def __str__(self):
        # type: () -> str
        return 'running %s on %s' % (self.solver.origname,
                                     self.filename)

    def __repr__(self):
        # type: () -> str
        return 'OfflineSolverExecution(%r,%r,%r)' % (self.solver,
                                                     self.process,
                                                     self.filename)

    def kill(self):
        # type: () -> None
        """Terminate the offline solver process associated with this instance."""
        if not self.dead:
            try:
                os.killpg(self.process.pid, signal.SIGTERM)
                self.stdout.close()
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait()
            except OSError, e:
                pass  # the process was already dead
        self.dead = True

    # required for compatibility with IO multiplexing using the select module
    def fileno(self):
        # type: () -> int
        return self.stdout.fileno()


class PersistableModel(MutableMapping):  # unchecked!
    """A dictionary representing a countermodel returned by an SMT solver query.

    Solver context methods returning or manipulating `PersistableModel`s may
    decide that the model is incomplete with respect to the current context if
    e.g. the model omits some model variables. If so, the model will contain
    the "canary" key 'IsIncomplete' to indicate this.

    `PersistableModel`s can be used in place of Python dicts. Calling the
    `persist()` method of the instance will prevent further changes to the
    underlying dictionary of the instance.

    Attributes:
        is_incomplete: True if the underlying dictionary contains the incomplete model canary.
    """
    def __init__(self, dict_to_persist):
        self.store = copy.deepcopy(dict_to_persist)
        self.persisted = False
        self.is_incomplete = False
        if ('IsIncomplete', None) in self.store:
            # del self.store[('IsIncomplete', None)]
            self.is_incomplete = True

    def persist(self):
        """Prevents further modification of the model.

        After this method is called on a given instance, all attempts to modify
        the underlying dictionary of this model using the `PersistableModel`
        interface will fail with an exception.

        Note that the underlying dictionary itself does not become read-only,
        and may be modified by invoking setter methods directly on the
        underlying dictionary.
        """
        self.persisted = True

    def copy(self):
        """Returns a (non-persisted, disjoint) copy of the model."""
        return PersistableModel(copy.deepcopy(self.store))

    def __getitem__(self, key):
        return self.store[key]

    def __setitem__(self, key, value):
        if self.persisted:
            raise ValueError("persisted PersistableModel object doesn't support item assignment")
        self.store[key] = value

    def __delitem__(self, key):
        if self.persisted:
            raise ValueError("persisted PersistableModel object doesn't support item deletion")
        del self.store[key]

    def __iter__(self):
        if self.persisted:
            return iter(copy.deepcopy(self.store))
        return iter(self.store)

    def __len__(self):
        return len(self.store)


class LoggerProtocol(Protocol):
    """A simple protocol for injecting logging.

    Provides basic functionality for logging process info, so we don't pollute
    stdout with constant prints.

    Should be replaced by Python's `logging` once we migrate to Python3 and
    eliminate the old `trace()` and `printout()` functions from the not-yet-
    typechecked parts of `graph-refine`.
    """

    def info(self, the_message):
        # type: (str) -> None
        """Logs the given message indicating that things are working as expected.

        Args:
            the_message: The given message.
        """
        raise NotImplementedError

    def warning(self, the_message):
        # type: (str) -> None
        """Logs the given message indicating that something unexpected happened.

        A warning usually indicates that something rare or unexpected happened,
        or that we are on a path that could hit some problem in the near future
        (such as `low disk space`), but the program still works as expected.

        Args:
            the_message: The given message.
        """
        raise NotImplementedError

    def error(self, the_message):
        # type: (str) -> None
        """Logs the given message indicating that a serious error has occurred.

        An error usually indicates that the program has been unable to perform
        a requested function due to a contract violation or other serious
        issue. The program itself may be unable to continue running.

        Args:
            the_message: The given message.
        """
        raise NotImplementedError

    def raw_print(self, the_message):
        # type: (str) -> None
        raise NotImplementedError


class PrintLogger:  # implements LoggerProtocol
    """A logger that prints all its messages to stdout."""
    def __init__(self, the_tag):
        # type: (str) -> None
        self.tag = the_tag

    def info(self, the_message):
        # type: (str) -> None
        current_function = inspect.stack()[1][3]
        self.raw_print('%s %s: %s' % (self.tag, current_function, the_message))

    def warning(self, the_message):
        # type: (str) -> None
        current_function = inspect.stack()[1][3]
        self.raw_print('%s warn %s: %s' % (self.tag, current_function, the_message))

    def error(self, the_message):
        # type: (str) -> None
        current_function = inspect.stack()[1][3]
        self.raw_print('%s error %s: %s' % (self.tag, current_function, the_message))

    def raw_print(self, the_message):
        # type: (str) -> None
        print the_message


class ErrorOnlyLogger:  # implements LoggerProtocol
    """A logger that prints only errors and raw messages to stdout."""

    def __init__(self, the_tag):
        # type: (str) -> None
        self.tag = the_tag

    def set_function(self, function_name):
        # type: (str) -> None
        self.current_function = function_name

    def info(self, the_message):
        # type: (str) -> None
        pass

    def warning(self, the_message):
        # type: (str) -> None
        pass

    def error(self, the_message):
        # type: (str) -> None
        current_function = inspect.stack()[1][3]
        self.raw_print('%s error %s: %s' % (self.tag, current_function, the_message))

    def raw_print(self, the_message):
        # type: (str) -> None
        print the_message


# FIXME: remove this legacy class
class ParallelSolversEntry:
    def __init__(self, hypotheses, execution, model):
        # type: (List[Hypothesis], OfflineSolverExecution, Optional[PersistableModel]) -> None
        self.hypotheses = hypotheses
        self.execution = execution
        self.model = model
