# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause

# You must have the typing module in your Python2.7 search path.
# Use `pip2.7 install typing` to install the module.
from typing import (Any, Dict, IO, List, NamedTuple, Optional, Set, Tuple, Union)

# will probably change in Python3+, not sure how
from StringIO import StringIO

# backported from Python3.4, use pip2.7 install enum34
from enum import Enum

import copy
import os
import select
import signal
import subprocess

import typed_commons
from typed_commons import (CMIAbort, CMIContinue, CMIResult, CheckModelIterationState, CheckModelIterationVerdict, Hypothesis, LoggerProtocol, PersistableModel, PrintLogger, SMTExpr, OfflineSolverExecution, SolverContextProtocol, SolverImpl, VariableEnvironment)

import syntax

# Implementor's notes:
#
# While proving trace refinement, `graph-refine` tends to send large queries
# to SMT solvers. To guarantee good performance (given CPU cycles to burn),
# these queries are best sent to multiple different solvers that run in
# parallel in 'offline' mode (i.e. one dedicated process for each query),
# so that we can take the result from whichever solver returns first.
#
# Running solvers in parallel allows us to exploit the specific performance
# characteristics of different SMT algorithms/implementations, and even lets
# us test the same problem in both the 8-bit and the 32/64-bit (arch-native)
# memory representations.
#
# The `graph-refine` tool uses a 'model-guided' validation process: heuristics
# picking plausible-looking relations between binary and C nodes, with all
# relevant registers related to available C variables of 'matching' types.
# At first, these relations are unlikely to be valid, but `graph-refine` can
# make a request to an SMT solver to produce a model in which the nodes are
# hit, but the relation we picked fails to hold. If the solver indicates that
# the desired conditions are unsatisfiabile ('unsat'), then we have found a
# valid relation; otherwise, the solver responds with the appropriate model,
# which narrows the future iterations of the heuristic search substantially,
# since the model can be used to eliminate more path-condition equalities and
# variable relations than just the ones that were explicitly tested.
#
# Unfortunately, the SMT solvers often return incomplete ("bogus") models,
# which need to be refined via additional queries: this is the so-called
# 'model repair' process.
#
# The purpose of the parallel solvers mechanism (`ParallelTaskManager`) is to
# control and coordinate the execution of parallel solvers. It is provided with
# a list of hypotheses (the 'goals'), and sends them to SMT solvers in parallel
# in an attempt to either confirm all the goals, or refute one of them. In the
# latter case, the `ParallelTaskManager` should also ensure that the provided
# countermodel is not bogus, by executing the model repair procedure if
# necessary.
#
# ---
#
# Implementation-specific Glossary:
#     hypothesis:
#         A predicate that can be converted to an SMTLIB2-compatible assertion.
#     goal:
#         A hypothesis that the current parallel query is supposed to confirm,
#         and could potentially refute with a counter-model.
#     execution:
#         The process of a currently running SMT solver implementation, along
#         with its associated state (IO streams, filenames, etc.)
#     task:
#         A single query sent to a singel SMT solver implementation, with the
#         aim of confirming or refuting a given list of goals.
#     prove task:
#         A task that aims to directly confirm or refute a conjunction of
#         goals by asking an SMT solver to produce a counter-model.
#     model repair task:
#         A task that indirectly aims to confirm or refute a conjunction of
#         goals (of another, specified task), by repairing a 'bogus' counter-
#         model previously returned by another task.
#     cancelled (task state):
#         A task whose associated process was deliberately terminated by the
#         `ParallelTaskManager` before it could produce a result. Usually,
#         this happens because the task became redundant during its execution.
#     failed (task state):
#         A task whose associated process returned, but without confirming or
#         refuting any of the goals of the task.
#     parent:
#         The solver context that instantiated the `ParallelTaskManager`.
#
# Implementation details:
#
# `ParallelTaskManager` is built around (and encapsulates) a single piece of
# mutable state, the 'task pool'. The task pool is a dictionary of tasks
# indexed by unique task identifiers. The pool contains information about all
# the tasks that are currently executing, as well as the tasks that have
# finished executing, and acts as a single source of truth throughout the
# parallel search process. Any other information required to make decisions
# about task management can be (and _is_) calculated on demand by inspecting
# the state of the task pool.
#
# Since the pool contains info about all the tasks that have ever executed,
# the size of the task pool is guaranteed never to decrease throughout the
# search process (i.e. no information is lost).


Key = int
KeyedHypothesis = Tuple[Key, Hypothesis]

SMTResponse = List[str]

class TaskStrategy(Enum):
    ALL = 0
    HYP = 1


class TaskOutcome(Enum):
    confirmed_all = 0
    refuted_some = 1
    sent_for_model_repair = 2
    cancelled = 3
    failed = 4


TaskStateFinished = NamedTuple('TaskStateFinished', [('solver', SolverImpl),
                                                     ('filename', str),
                                                     ('outcome', TaskOutcome),
                                                     ('raw_response', SMTResponse)])
TaskState = Union[OfflineSolverExecution, TaskStateFinished]
# TaskState.__doc__ = """Stores the state of an offline SMT solver query that
# has finished executing and returned a result.
#
# Attributes:
#     solver: The solver implementation that handled the resolved query.
#     filename: The name of the file containing the resolved query.
#     outcome: The outcome, as determined by interpreting the raw output of the SMT solver.
#     raw_response: The full response written by the SMT solver to its standard output, as a list of lines.
# """

TaskId = NamedTuple('TaskId', [('to_int', int)])

ProveTask = NamedTuple('ProveTask', [('goals', List[KeyedHypothesis]),
                                     ('strategy', TaskStrategy),
                                     ('model', Optional[PersistableModel]),
                                     ('state', TaskState)])
# ProveTask.__doc__ = """A task that was created to confirm or refute a given conjunction of hypotheses.
#
# The purpose of a `ProveTask` is to confirm or refute a given conjunction of
# goal hypotheses, by sending a query to all eligible solvers in parallel, and
# waiting for at least one of them to respond.
#
# If the task resolves with one of the solver refuting the conjunction,
# a counter-model can be obtained. This counter-model will be built by using
# the solver's output to update the model given in the `model` attribute.
#
# Attributes:
#     goals: The given goals whose conjunction is to be confirmed/refuted.
#     strategy: If ALL, should be executed by a solver on the 'all' solverlist, otherwise one on the 'hyp' solverlist.
#     model: If not `None`, base any potential countermodel on this one. If `None`, do not obtain countermodels.
#     state: The execution state of the task.
# """

ModelRepairTask = NamedTuple('ModelRepairTask', [('provenance', TaskId),
                                                 ('check_model_iteration_result_state', CheckModelIterationState),
                                                 ('sent_hypotheses', List[KeyedHypothesis]),
                                                 ('model', PersistableModel),
                                                 ('state', TaskState)])
# ModelRepairTask.__doc__ = """A task that was created to repair a counter-model to some hypothesis.
#
# When an SMT solver refutes one of the goals (or a conjunction thereof), it
# provides a countermodel, a variable assignment which makes the relevant
# hypotheses false. Unfortunately, these returned models can be incomplete,
# as determined by a 'bogus model check'.
#
# The purpose of a `ModelRepairTask` is to obtain a more complete countermodel
# to a previously refuted goal. Multiple iterations of the model repair
# procedure (followed by a bogus model check) may be required to fully repair
# a countermodel.
#
# Every `ModelRepairTask` keeps track of its own `provenance`, the finished
# task which triggered the execution of the model repair. This may be a refuted
# `ProveTask` (if the returned model was bogus), or it may be a previous
# `ModelRepairTask` (if its model repair procedure was finished, but the bogus
# model check determined that further repairs are required).
#
# The result of a `ModelRepairTask` is a more complete counter-model. This
# counter-model will be built by using the solver's output to update the model
# stored in the `model` attribute of the task.
#
# Attributes:
#     provenance: The id of the finished task which triggered this task.
#     check_model_iteration_result_state: Saved state of the bogus model check.
#     sent_hypotheses: The list of hypotheses sent to the SMT solver.
#     model: The counter-model to update.
# """

Task = Union[ProveTask, ModelRepairTask]


class ParallelTaskManager:
    def __init__(self, parent, goals, environment, model, log=PrintLogger("PTM")):
        # type: (SolverContextProtocol, List[KeyedHypothesis], VariableEnvironment, Optional[PersistableModel], LoggerProtocol) -> None
        self.parent = parent
        self.goals = goals
        self.environment = environment
        self.model = model
        self.task_pool = {}  # type: Dict[TaskId, Task]
        self.log = log

    # wrapped syntax function helps the type-checker
    def wrap_syntax_mk_not(self, x):
        # (Any) -> Any
        return syntax.mk_not(x)

    # wrapped syntax function helps the type-checker
    def wrap_syntax_mk_and(self, x, y):
        # (Any,Any) -> Any
        return syntax.mk_and(x, y)

    # wrapped syntax function helps the type-checker
    def wrap_syntax_foldr1(self, f, xs):
        # (Any, Any) -> Any
        return syntax.foldr1(f, xs)

    def smt_expr_from_goals(self, the_goals):
        # type: (List[KeyedHypothesis]) -> SMTExpr
        """Returns an assertable SMT expression stating that the given goals can fail to hold.

        The elements constituting the given list of hypotheses are required
        to be 'goals', not arbitrary hypotheses (say ones generated as part
        of the model repair procedure). This is because we're looking to find
        counter-models to the goals, so the returned assertable `SMTExpr` will
        state that one of the goals fails to hold.

        Args:
            the_goals: The given goals.
        """
        hypotheses = [h for (k, h) in the_goals]
        # we want counter-models, so we negate everything in sight
        gr_hypothesis = self.wrap_syntax_mk_not(self.wrap_syntax_foldr1(self.wrap_syntax_mk_and, hypotheses))
        return self.parent.smt_expr(gr_hypothesis, self.environment)

    def state_with_outcome(self, the_state, with_outcome):
        # type: (TaskStateFinished, TaskOutcome) -> TaskStateFinished
        """Returns a copy of the given state, with the value of the `outcome` field replaced by the given outcome.

        Note that this does not perform an in-place update: `TaskState`s are
        immutable, so we return a modified copy instead.

        Args:
            the_state: The given state.
            with_outcome: The given outcome (resulting value of the `outcome` field).
        """
        new_state = TaskStateFinished(the_state.solver,
                                      the_state.filename,
                                      with_outcome,
                                      the_state.raw_response)
        return new_state

    def task_with_state(self, the_task, with_state):
        # type: (Task, TaskState) -> Task
        """Returns a copy of the given `Task`, with the value of the `state` field replaced by the given state.

        Note that this does not constitute an in-place update: `Task` objects
        are immutable, so we return a modified copy instead.

        Args:
            the_task: The given task.
            the_state: The given state (resulting value of the `state` field).
        """
        if isinstance(the_task, ProveTask):
            return ProveTask(the_task.goals,
                             the_task.strategy,
                             the_task.model,
                             with_state)
        elif isinstance(the_task, ModelRepairTask):
            return ModelRepairTask(the_task.provenance,
                                   the_task.check_model_iteration_result_state,
                                   the_task.sent_hypotheses,
                                   the_task.model,
                                   with_state)
        raise TypeError('inexhaustive pattern, unknown Task type %r' % type(the_task))

    def extract_outcome_from_smt_response(self, the_raw_response):
        # type: (SMTResponse) -> TaskOutcome
        """Returns the outcome of a task by parsing its given SMT response.

        SMTLIB2-compatible solver implementations respond to the `(check-sat)`
        command by searching for a model that satisfies all the previously
        asserted formulae. Once the search concludes, the solver prints a
        one-line response to its output. A 'sat' response indicates that the
        solver has found a model, while an 'unsat' response indicates that
        the solver has established the non-existence of such models. Other
        responses, including 'unknown' or the empty string '' indicate that an
        error occurred, or the search was otherwise inconclusive.

        The `extract-*` methods assume that they are reading the response to a
        query emitted by `start_execution`: such queries contain a single
        `(check-sat)` command, potentially followed by a `(get-model)` command,
        and no other output-producing commands. Consequently, we assume that
        the response consist of a one-line `(check-sat)` response, potentially
        followed by a multi-line `(get-model)` response.

        This function parses the response, and determines the outcome of the
        task that emitted the query (with respect to the associated goals).

        Args:
            the_raw_response: The given raw response (to be parsed).
        """
        if len(the_raw_response) < 1:
            self.log.warning('failed to extract outcome, response was empty')
            return TaskOutcome.failed
        headline = the_raw_response[0].strip()
        if headline == 'unsat':
            return TaskOutcome.confirmed_all
        if headline == 'sat':
            return TaskOutcome.refuted_some
        self.log.warning("failed to extract outcome, expected 'sat' or 'unsat', got %r" % headline)
        return TaskOutcome.failed

    def extract_model_from_smt_response(self, the_raw_response):
        # type: (SMTResponse) -> Optional[PersistableModel]
        """Returns the model returned by a refuting task, by parsing its given SMT response.

        SMTLIB2-compatible solver implementations respnod to the `(get-model)`
        command by printing a list of SMTLIB definitions specifying values of
        all (and only) the user-declared function symbols in a previously found
        model satisfying all the previously asserted formulae.
        (cf. `extract_outcome_from_smt_response`). An error report is printed
        if no such model has been found.

        The `extract-*` methods assume that they are reading the response to a
        query emitted by `start_execution`: such queries contain a single
        `(check-sat)` command, potentially followed by a `(get-model)` command,
        and no other output-producing commands. Consequently, we assume that
        the response consist of a one-line `(check-sat)` response, potentially
        followed by a multi-line `(get-model)` response.

        This function parses the response, and creates a `PersistableModel`
        instance mapping the user-declared function symbols to their
        definitions.

        Args:
            the_raw_response: The given raw response (to be parsed).
        """
        if len(the_raw_response) == 0:
            self.log.warning('failed to extract model, response was empty')
            return None
        # fetch_model_response used to operate straight on the stdout of the solver,
        # but was called after the first line of the stdout stream was consumed.
        # we "fake" this behavior by turning the raw output into a stream.
        the_model = PersistableModel({})
        faux_stream = StringIO('\n'.join(the_raw_response[1:]))  # type: IO[str]
        got_result = self.parent.fetch_model_response(the_model, stream=faux_stream)
        if got_result is None:
            # model could not be parsed, or was malformed
            self.log.warning('failed to extract model, no parse')
            return None
        return the_model

    def get_task_by_id(self, task_id):
        # type: (TaskId) -> Task
        """Returns the task currently associated with the given `TaskId` in the task pool.

        Args:
            task_id: The given task id.
        """
        if task_id not in self.task_pool:
            # Note that we avoid `Optional[Task]` for a reason:
            # We don't expect invalid `TaskId`s to arise from thin air, and thus
            # something must have gone wrong if we found ourselves here.
            self.log.error('no task with id %s' % task_id.to_int)
            raise KeyError(task_id)
        return self.task_pool[task_id]

    def cancel_task_by_id(self, task_id):
        # type: (TaskId) -> None
        """Cancels the execution of the task in the task pool with the given task id.

        Args:
            task_id: The given task id (whose execution is to be cancelled).
        """
        the_task = self.get_task_by_id(task_id)
        if not isinstance(the_task.state, OfflineSolverExecution):
            self.log.error('cannot cancel non-running task of id %s' % task_id.to_int)
            raise TypeError('expected OfflineSolverExecution, got %s' % type(the_task.state))
        assert isinstance(the_task.state, OfflineSolverExecution)
        new_state = TaskStateFinished(the_task.state.solver, the_task.state.filename, TaskOutcome.cancelled, [])
        the_task.state.kill()
        self.task_pool[task_id] = self.task_with_state(the_task, new_state)
        return None

    def _task_id_to_int(self, task_id):
        # type: (TaskId) -> int
        # workaround for a mypy bug involving 1-element `NamedTuple`s in "for comprehensions"
        return task_id.to_int

    def add_task_to_pool(self, the_task):
        # type: (Task) -> TaskId
        """Adds the given task to the task pool with a fresh task id, returning the task id.

        Note: this is the only way to mint a new task id.

        Args:
            the_task: The given task (to be added to the pool).
        """
        # we should probably check that we're not adding the same task twice
        indices = [self._task_id_to_int(i) for i in self.task_pool.keys()]  # type: List[int]
        next_index = 0 if len(indices) == 0 else max(indices) + 1
        self.task_pool[TaskId(next_index)] = the_task
        return TaskId(next_index)

    def get_goals_by_id(self, task_id):
        # type: (TaskId) -> List[KeyedHypothesis]
        """Returns the goals that would be confirmed if the task with the given task id was confirmed.

        Args:
            task_id: The given task id.
        """
        the_task = self.get_task_by_id(task_id)
        if isinstance(the_task, ProveTask):
            return the_task.goals
        elif isinstance(the_task, ModelRepairTask):
            return self.get_goals_by_id(the_task.provenance)
        raise TypeError('inexhaustive pattern, unknown Task type %r' % type(the_task))

    def get_strategy_by_id(self, task_id):
        # type: (TaskId) -> TaskStrategy
        """Returns the task strategy associated with the task with the given task id.

        Note: each solver implementation (`SolverImpl`) has an associated
        strategy (ALL or HYP) determined by the solver context and configured
        in a solverlist file. This `TaskStrategy` is used to determine which
        solvers receive a particular query. Generally, tasks that attempt to
        confirm all goals at once use the ALL strategy, while tasks that aim to
        confirm or refute a single hypothesis use the HYP strategy.

        Args:
            task_id: The given task id.
        """
        the_task = self.get_task_by_id(task_id)
        if isinstance(the_task, ProveTask):
            return the_task.strategy
        elif isinstance(the_task, ModelRepairTask):
            return self.get_strategy_by_id(the_task.provenance)
        raise TypeError('inexhaustive pattern, unknown Task type %r' % type(the_task))

    def get_solvers_by_strategy(self, the_strategy):
        # type: (TaskStrategy) -> List[SolverImpl]
        """Returns a list of SMT solver implementations suitable for use with the given task strategy.

        Note: each solver implementation (`SolverImpl`) has an associated
        strategy (ALL or HYP) determined by the solver context and configured
        in a solverlist file. This `TaskStrategy` is used to determine which
        solvers receive a particular query. Generally, tasks that attempt to
        confirm all goals at once use the ALL strategy, while tasks that aim to
        confirm or refute a single hypothesis use the HYP strategy.

        Args:
            the_strategy: The given strategy.
        """
        result = []  # type: List[SolverImpl]
        if the_strategy == TaskStrategy.ALL:
            result = [solver for (solver, strat) in self.parent.get_strategy() if strat == 'all']
        elif the_strategy == TaskStrategy.HYP:
            result = [solver for (solver, strat) in self.parent.get_strategy() if strat == 'hyp']
        else:
            raise TypeError('inexhaustive pattern, unknown TaskStrategy type %r' % the_strategy)
        if len(result) > 0:
            return result
        self.log.error('no solvers found for strategy %s' % the_strategy)
        raise ValueError('no solvers found for strategy %s' % the_strategy)

    def start_execution(self, the_hypotheses, the_model, the_solver):
        # type: (List[SMTExpr], Optional[PersistableModel], SolverImpl) -> OfflineSolverExecution
        """Executes the given SMT solver implementation with the given hypotheses, returning an `OfflineSolverExecution` instance containing the resulting process and script file.

        Args:
            the_hypotheses: The given hypotheses (to be sent to the solver).
            the_model: If not None, generate a request to fetch model values.
            the_solver: The given SMT solver implementation (which is to execute the query).
        """
        smt_cmds = []  # type: List[str]
        for h in the_hypotheses:
            smt_cmds.append('(assert %s)' % str(h))
        smt_cmds.append('(check-sat)')
        if the_model is not None:
            smt_cmds.append(self.parent.fetch_model_request())
        return self.parent.exec_slow_solver(smt_cmds, timeout=the_solver.timeout, solver=the_solver)

    def start_prove_task_with_solver(self, goals, strategy, model, the_solver):
        # type: (List[KeyedHypothesis], TaskStrategy, Optional[PersistableModel], SolverImpl) -> TaskId
        """Start a task with the aim of confirming or refuting the given goals, using the given SMT solver implementation.

        Args:
            goals: The given goals (to be confirmed or refuted).
            strategy: The given task strategy.
            model: The base model. If not `None`, generate a request to fetch values from the resulting counter-model.
            the_solver: The given solver (to be used to settle the query).
        """
        smt_hypothesis = self.smt_expr_from_goals(goals)
        execution = self.start_execution([smt_hypothesis], model, the_solver)
        new_task = ProveTask(goals, strategy, model, execution)
        return self.add_task_to_pool(new_task)

    def start_prove_task(self, goals, strategy):
        # type: (List[KeyedHypothesis], TaskStrategy) -> List[TaskId]
        """Start parallel tasks with the aim of confirming or refuting the given goals, using all solvers configured for the given strategy.

        Args:
            goals: The given goals (to be confirmed or refuted).
            strategy: The given strategy (used to choose the solvers).
        """
        if len(goals) == 0:
            self.log.error('attempted to prove zero goals')
            raise ValueError('list of goals must be non-empty')
        self.log.info('starting prove task for %s goal(s)' % len(goals))
        solvers = self.get_solvers_by_strategy(strategy)
        model = None  # Optional[PersistableModel]
        if self.model is not None:
            model = self.model.copy()
        return [self.start_prove_task_with_solver(goals, strategy, model, solver) for solver in solvers]

    def start_model_repair_task(self, original_task_id, original_task_model, check_model_iteration_result):
        # type: (TaskId, PersistableModel, CMIContinue) -> TaskId
        """Start a task with the aim of repairing a given bogus model returned by a previously executed task.

        Args:
            original_task_id: The task id of the previously executed task which returned the bogus model.
            original_task_model: The given bogus model (to be repaired).
            check_model_iteration_result: The result of the bogus model check which triggered the start of this model repair task.
        """
        self.log.info('starting model repair task for %s hypotheses' % len(check_model_iteration_result.next_hypotheses))
        new_task_model = original_task_model.copy()
        execution = self.start_execution(check_model_iteration_result.next_hypotheses,
                                         new_task_model,
                                         check_model_iteration_result.next_solver)
        new_task = ModelRepairTask(provenance=original_task_id,
                                   check_model_iteration_result_state=check_model_iteration_result.state,
                                   sent_hypotheses=check_model_iteration_result.next_hypotheses,
                                   model=new_task_model,
                                   state=execution)
        return self.add_task_to_pool(new_task)


    def restart_model_repair_task_change_solver(self, task_id):
        # type: (TaskId) -> Optional[TaskId]
        """Restarts the failed model repair task with the given id using the next available solver.

        Some SMT solver implementations may enter various error states, such as
        segfaults, while performing the model repair process on a model emitted
        by a prove task. Since model repairs are not parallel, in the sense
        that only one solver works on repairing any given model at any point in
        time, such failures may cause the search to stall (with `timeout`).

        This function allows us to restart failed model repair tasks with the
        next available solver, skipping the failing solver, and ensuring that
        we do not prematurely abandon a model repair attempt due to the failure
        of the solver we tried first.

        Args:
            task_id: The given task id (of the task to be restarted).
        """
        # Uses `TaskId` instead of `ModelRepairTask` since we need to keep
        # track of provenance. Fixes the "segfaulting SONOLAR" bug.
        the_task = self.get_task_by_id(task_id)
        if not isinstance(the_task, ModelRepairTask):
            self.log.info('no need to change solver, given task is not ModelRepair')
            return None
        assert isinstance(the_task, ModelRepairTask)
        if not isinstance(the_task.state, TaskStateFinished):
            self.log.info('no need to change solver, given task is still running')
            return None
        assert isinstance(the_task.state, TaskStateFinished)
        if the_task.state.outcome != TaskOutcome.failed:
            self.log.info('no need to change solver, given task did not fail')
            return None
        assert the_task.state.outcome == TaskOutcome.failed
        the_cmi_state = the_task.check_model_iteration_result_state
        next_solvers = the_cmi_state.remaining_solvers  # type: List[SolverImpl]
        if len(next_solvers) == 0:
            self.log.warning('cannot change solver, no further solvers to try')
            return None
        self.log.info('restarting task with next solver')
        new_candidate_model = the_cmi_state.candidate_model.copy() if the_cmi_state.candidate_model is not None else None
        new_cmi_state = CheckModelIterationState(the_cmi_state.confirmed_hypotheses,
                                                 the_cmi_state.test_hypotheses,
                                                 new_candidate_model,
                                                 next_solvers[1:])
        new_task_model = the_task.model.copy()
        execution = self.start_execution(the_task.sent_hypotheses,
                                         new_task_model,
                                         next_solvers[0])
        new_task = ModelRepairTask(provenance=task_id,
                                   check_model_iteration_result_state=new_cmi_state,
                                   sent_hypotheses=the_task.sent_hypotheses,
                                   model=new_task_model,
                                   state=execution)
        return self.add_task_to_pool(new_task)

    def perform_bogus_model_check(self, task_id):
        # type: (TaskId) -> None
        """Checks if the task with the given id has produced a bogus or invalid counter-model, and if so, initiates model repair tasks.

        When a prove task ends with the refutation of a given goal, we may ask
        for a counter-model. The counter-models provided by the SMT solvers
        often end up incomplete ('bogus'): if so, additional model repair tasks
        have to be executed to refine them into complete models usable by the
        'model-guided' search heuristics of `graph-refine`.

        This function is responsible for checking if the task with the given id
        has produced such a bogus model. If so, it starts the appropriate model
        repair tasks. Note that a model repair task may itself produce another
        bogus model, in which case another model repair task may be started.

        In some cases, the bogus model check can indicate that further repairs
        to the current bogus model are futile and won't result in a usable
        counter-model. If so, the model repair task is considered a failure and
        is abandoned.

        Args:
            task_id: The given task id.
        """
        the_task = self.get_task_by_id(task_id)
        if the_task.model is None:
            # we won't be returning the model, so we can skip this check
            self.log.info('check elided, no model will be returned')
            return None
        assert the_task.model is not None
        if not isinstance(the_task.state, TaskStateFinished):
            self.log.info('check elided, given task is still running')
            return None
        assert isinstance(the_task.state, TaskStateFinished)
        if the_task.state.outcome != TaskOutcome.refuted_some:
            if isinstance(the_task, ProveTask):
                # on ModelRepair, we abort later due to inconsistent sat/unsat
                self.log.info('check elided, given task did not refute any hypotheses')
                return None
            if isinstance(the_task, ModelRepairTask) and the_task.state.outcome == TaskOutcome.failed:
                self.log.warning('given task may have failed due to faulty solver, changing solver')
                self.restart_model_repair_task_change_solver(task_id)
        response_model = self.extract_model_from_smt_response(the_task.state.raw_response)
        if response_model is None:
            # The SMT solver claims to have refuted some of our hypotheses, but it did not provide a counter-model
            # that we could parse. In accordance with the previous parallel solvers mechanism, we treat this as a
            # failed (erroneous) SMT query.
            self.log.warning('counter-model not found or could not be parsed, SMT query failed')
            the_task.model.persist()
            finished_state = self.state_with_outcome(the_task.state, TaskOutcome.failed)
            self.task_pool[task_id] = self.task_with_state(the_task, finished_state)
            return None
        assert response_model is not None
        smt_hypothesis = self.smt_expr_from_goals(self.get_goals_by_id(task_id))
        state = the_task.check_model_iteration_result_state if isinstance(the_task, ModelRepairTask) else None
        response_line = the_task.state.raw_response[0].strip() if len(the_task.state.raw_response) > 0 else 'unknown'
        cmi_verdict = self.parent.check_model_iteration([smt_hypothesis], state, (response_line, response_model))
        if isinstance(cmi_verdict, CMIAbort):
            # The model is still bogus (incomplete), but the check suggests that no further repair is possible:
            # we have either tried all the solvers, or got inconsistent results. In accordance with the previous
            # parallel solvers mechanism, we treat this as a failed SMT query.
            self.log.info('model is incomplete, irreparable')
            the_task.model.persist()
            finished_state = self.state_with_outcome(the_task.state, TaskOutcome.failed)
            self.task_pool[task_id] = self.task_with_state(the_task, finished_state)
            return None
        elif isinstance(cmi_verdict, CMIContinue):
            # The model is still bogus (incomplete), but we might be able to repair it by spawning a ModelRepair task.
            self.log.info('model is incomplete, requires repair')
            the_task.model.persist()
            finished_state = self.state_with_outcome(the_task.state, TaskOutcome.sent_for_model_repair)
            self.task_pool[task_id] = self.task_with_state(the_task, finished_state)
            self.start_model_repair_task(task_id, the_task.model, cmi_verdict)
            return None
        elif isinstance(cmi_verdict, CMIResult):
            # We passed the check, and the model is complete. We return it.
            self.log.info('model is complete, check passed')
            the_task.model.update(cmi_verdict.candidate_model)
            the_task.model.persist()
            return None
        raise TypeError('inexhaustive pattern, unknown CheckModelIterationVerdict type %r' % type(cmi_verdict))

    def handle_progress(self, task_id):
        # type: (TaskId) -> None
        """Updates the task pool according to the result of the finished task with the given task id.

        Whenever an SMT solver implementation finishes its execution on a task,
        the task outcome has to be determined, and the task pool has to be
        updated to reflect the changed status of the task. Moreover, if the
        SMT solver produced a refutation, other, auxiliary tasks such as model
        repairs may have to be performed. This function performs the required
        updates and starts the required auxiliary tasks.

        Args:
            task_id: The given task id (whose progress is to be assessed).
        """
        the_task = self.get_task_by_id(task_id)
        original_state = the_task.state
        if not isinstance(original_state, OfflineSolverExecution):
            self.log.error('unable to read output, given task not running')
            raise TypeError('expected OfflineSolverExecution, got %s' % type(original_state))
        assert isinstance(original_state, OfflineSolverExecution)
        out, err = original_state.process.communicate()
        the_raw_response = out.splitlines()
        original_state.kill()
        the_outcome = self.extract_outcome_from_smt_response(the_raw_response)  # type: TaskOutcome
        finished_state = TaskStateFinished(original_state.solver, original_state.filename, the_outcome, the_raw_response)
        self.task_pool[task_id] = self.task_with_state(the_task, finished_state)
        self.perform_bogus_model_check(task_id)
        return None

    def wait_for_progress(self):
        # type: () -> List[TaskId]
        """Synchronously monitors the currently running tasks until one or more of them make progrss, then returns a list of task ids that made progress.

        This function monitors the file descriptors of the currently running
        tasks (as given in the task pool), waiting until one or more of the
        descriptors become 'ready to read'. The task ids of the tasks that
        are associated to the ready to read file descriptors are returned.
        """
        running_tasks = [(task.state, id) for (id, task) in self.task_pool.iteritems() if isinstance(task.state, OfflineSolverExecution)]  # type: List[Tuple[OfflineSolverExecution, TaskId]]
        running_executions = [state for (state, id) in running_tasks]  # type: List[OfflineSolverExecution]
        # synchronously wait for IO completion using select:
        # eventually returns a list of ready-to-read OfflineSolverExecution objects
        (ready_to_read, _, _) = select.select(running_executions, [], [])
        task_id_by_execution = dict(running_tasks)
        return [task_id_by_execution[execution] for execution in ready_to_read]

    def collect_explicit_refutations(self):
        # type: () -> List[TaskId]
        """Returns the list of all current explicit refutations in the task pool.

        A task is considered a 'refutation' if it finished with one or more of
        the associated goals (see above for the distinction between goals and
        other hypotheses) being refuted.

        If a refutation has multiple associated goals, then all we know is that
        we have a counter-model that refutes one of the goal hypotheses, but
        we may not know precisely which hypotheses were refuted. Currently,
        `graph-refine` is not equipped to figure out the precise identity of
        the refuted hypotheses. Hence, we consider a refutation 'explicit' when
        it has exactly one associated goal.
        """
        refutations = []  # List[TaskId]
        for (id, task) in self.task_pool.iteritems():
            if isinstance(task.state, TaskStateFinished):
                is_refutation = task.state.outcome == TaskOutcome.refuted_some
                is_explicit = len(self.get_goals_by_id(id)) == 1
                if is_refutation and is_explicit:
                    refutations.append(id)
        return refutations

    def collect_confirmed_goals(self):
        # type: () -> Set[KeyedHypothesis]
        """Returns the set of all current goals that have been confirmed by any task in the task pool."""
        confirmed_goals = []  # type: List[KeyedHypothesis]
        for (id, task) in self.task_pool.iteritems():
            if isinstance(task.state, TaskStateFinished) and task.state.outcome == TaskOutcome.confirmed_all:
                confirmed_goals.extend(self.get_goals_by_id(id))
        return set(confirmed_goals)

    def collect_explicit_refuted_goals(self):
        # type: () -> Set[KeyedHypothesis]
        """Returns the set of all current goals that have been explicitly refuted by some task in the task pool.

        See `collect_explicit_refutations` for the "refuted / explicit refuted"
        distinction.
        """
        explicit_refuted_goals = []  # List[TaskId]
        for (id, task) in self.task_pool.iteritems():
            if isinstance(task.state, TaskStateFinished):
                is_refutation = task.state.outcome == TaskOutcome.refuted_some
                task_goals = self.get_goals_by_id(id)
                is_explicit = len(task_goals) == 1
                if is_refutation and is_explicit:
                    explicit_refuted_goals.extend(task_goals)
        return set(explicit_refuted_goals)

    def collect_running_goals(self):
        # type: () -> Set[KeyedHypothesis]
        """Returns the set of all current goals that are associated to a currently running task in the task pool."""
        running_goals = []  # type: List[KeyedHypothesis]
        for (id, task) in self.task_pool.iteritems():
            if isinstance(task.state, OfflineSolverExecution):
                running_goals.extend(self.get_goals_by_id(id))
        return set(running_goals)

    def collect_explicit_running_goals(self):
        # type: () -> Set[KeyedHypothesis]
        """Returns the set of all current goals that are associated to a currently running explicit task in the task pool.

        A task is considered 'explicit' if it has exactly one associated goal.
        See `collect_explicit_refutations` for more on the "refuted / explicit
        refuted" distinction.
        """
        explicit_running_goals = []  # type: List[KeyedHypothesis]
        for (id, task) in self.task_pool.iteritems():
            if isinstance(task.state, OfflineSolverExecution) and self.get_strategy_by_id(id) == TaskStrategy.HYP:
                explicit_running_goals.extend(self.get_goals_by_id(id))
        return set(explicit_running_goals)

    def collect_explicit_failed_goals(self):
        # type: () -> Set[KeyedHypothesis]
        """Returns the set of all current goals whose associated explicit tasks have all finished and failed to produce a result.

        A task is considered 'explicit' if it has exactly one associated goal.
        See `collect_explicit_refutations` for more on the "refuted / explicit
        refuted" distinction.
        
        A goal that is not associated to any (running or finished) task is not
        considered failed: we consider a task failed only if we have started
        _explicit_ attempts to confirm or refute it, but all such attempts have
        ended in failure.
        """
        confirmed_goals = self.collect_confirmed_goals()
        explicit_refuted_goals = self.collect_explicit_refuted_goals()
        running_goals = self.collect_explicit_running_goals()
        excluded_goals = confirmed_goals.union(explicit_refuted_goals).union(running_goals)

        explicit_failed_goals = []  # type: List[KeyedHypothesis]
        for (id, task) in self.task_pool.iteritems():
            if isinstance(task.state, TaskStateFinished):
                is_failed = task.state.outcome == TaskOutcome.failed
                task_goals = set(self.get_goals_by_id(id))  # type: Set[KeyedHypothesis]
                is_explicit = len(task_goals) == 1
                if is_explicit and is_failed and task_goals.isdisjoint(excluded_goals):
                    explicit_failed_goals.extend(task_goals)
        return set(explicit_failed_goals)

    def collect_startable_goals(self):
        # type: () -> List[KeyedHypothesis]
        """Returns the set of all current goals for which an explicit task can still be started."""
        settled_goals = self.collect_confirmed_goals().union(self.collect_explicit_refuted_goals()).union(self.collect_explicit_failed_goals())
        return [goal for goal in self.goals if goal not in settled_goals]

    def cancel_redundant_tasks(self):
        # type: () -> None
        """Cancels all currently running redundant tasks in the task pool.

        A task is considered redundant if either
        a.) all its associated goals have already been confirmed; or
        b.) one of its associated goals has already been explicitly refuted;
        as determined by inspecting the task pool.

        Note that redundant tasks can always be safely cancelled: letting them
        run to completion would not increase the number of confirmed or
        explicit refuted hypotheses.
        """
        confirmed_goals = self.collect_confirmed_goals()
        refuted_goals = self.collect_explicit_refuted_goals()
        running_tasks = [id for (id, task) in self.task_pool.iteritems() if isinstance(task.state, OfflineSolverExecution)]
        for task_id in running_tasks:
            task_goals = set(self.get_goals_by_id(task_id))
            if not task_goals.isdisjoint(refuted_goals):
                self.log.info('task %s redundant, one of its goals is already refuted' % task_id.to_int)
                self.cancel_task_by_id(task_id)
            if task_goals.issubset(confirmed_goals):
                self.log.info('task %s redundant, all of its goals are already confirmed' % task_id.to_int)
                self.cancel_task_by_id(task_id)

    def cancel_all_tasks(self):
        # type: () -> None
        """Cancels all currently running tasks."""
        running_tasks = [id for (id, task) in self.task_pool.iteritems() if isinstance(task.state, OfflineSolverExecution)]
        for task_id in running_tasks:
            self.cancel_task_by_id(task_id)
        return None

    def start_next_explicit_goal(self):
        # type: () -> List[TaskId]
        """Starts an explicit prove task with the next startable goal (if there are any) as its only goal. Returns the list of tasks it started."""
        explicit_running_goals = self.collect_explicit_running_goals()
        if len(explicit_running_goals) > 0:
            self.log.info('cannot start new goal, other explicit goals still running')
            return []
        startable_goals = self.collect_startable_goals()
        if len(startable_goals) == 0:
            self.log.warning('cannot start new goal, no further goals to start')
            return []
        goal = startable_goals[0]
        return self.start_prove_task([goal], TaskStrategy.HYP)

    def print_task_pool(self):
        # type: () -> None
        """Prints a human-readable summary of the current state of the task pool."""
        self.log.raw_print('\ncurrent task pool:\n--- [')
        for (id, task) in self.task_pool.iteritems():
            outcome = 'running'  # type: str
            if isinstance(task.state, TaskStateFinished):
                outcome = '%s %s on %s' % (str(task.state.outcome)[12:], task.state.solver.origname, task.state.filename)
            elif isinstance(task.state, OfflineSolverExecution):
                outcome = str(task.state)
            outcome = outcome[:87]
            task_type = '   '
            if isinstance(task, ModelRepairTask):
                task_type = 'MR%s' % task.provenance.to_int
            elif isinstance(task, ProveTask):
                task_type = '%s' % (str(task.strategy)[13:])
            self.log.raw_print('%s %s %s' % (id.to_int, task_type, outcome))
        self.log.raw_print('--- ]\n')

    def main_loop(self):
        # type: () -> Tuple[str, Optional[Key], Optional[PersistableModel]]
        """Repeatedly performs task management operations until a termination condition is reached. Returns the final verdict.

        This function attempts to confirm all goals passed to the
        `ParallelTaskManager`. The loop monitors the task pool, and attempts to
        start new explicit prove tasks to settle as-yet-unconfirmed hypotheses.

        The loop terminates once all goals are confirmed; some goal is
        explicitly refuted; or there are no further tasks left to start.

        The final verdict is returned in the non-typechecked format expected by
        `parallel_check_hyps`.
        """
        if len(self.goals) > 1:
            self.start_prove_task(self.goals, TaskStrategy.ALL)
        target_goals = set(self.goals)

        while True:
            self.print_task_pool()
            confirmed_goals = self.collect_confirmed_goals()
            refutations = self.collect_explicit_refutations()
            running_goals = self.collect_running_goals()
            explicit_running_goals = self.collect_explicit_running_goals()

            self.log.info('checking termination conditions...')
            if len(refutations) > 0:
                # we have explicitly refuted some hypothesis
                refuted_task_id = refutations[0]  # type: TaskId
                refuted_model = self.get_task_by_id(refuted_task_id).model
                refuted_goals = self.get_goals_by_id(refuted_task_id)  # type: List[KeyedHypothesis]
                self.log.info('termination condition reached, task %s refuted a hypothesis' % refuted_task_id.to_int)
                self.cancel_all_tasks()
                assert len(refuted_goals) == 1
                return ('sat', refuted_goals[0][0], refuted_model)
            if target_goals.issubset(confirmed_goals):
                # we have confirmed all hypotheses
                self.log.info('termination condition reached, all hypotheses confirmed')
                self.cancel_all_tasks()
                return ('unsat', None, None)
            if len(explicit_running_goals) == 0:
                # no explicit tasks, try to start a new one
                started_tasks = self.start_next_explicit_goal()
                if len(started_tasks) == 0 and len(running_goals) == 0:
                    # there were no tasks left to start
                    self.log.warning('termination condition reached, all solvers failed or timed out')
                    return ('timeout', None, None)
            self.log.info('termination conditions not satisfied, continuing')

            self.log.info('waiting for SMT solvers to make progress...')
            progressed_tasks = self.wait_for_progress()  # type: List[TaskId]
            self.log.info('%s solver(s) made progress' % len(progressed_tasks))
            for task_id in progressed_tasks:
                self.log.info('handling progress on task %s' % task_id.to_int)
                self.handle_progress(task_id)
            self.log.info('handled progress from %s solver(s)' % len(progressed_tasks))

            self.cancel_redundant_tasks()
            continue

    def run(self):
        # type: () -> Tuple[str, Optional[Key], Optional[PersistableModel]]
        """Repeatedly performs task management operations on the task pool until all goals are confirmed, or some goal is explicitly refuted. Returns the final verdict.

        The final verdict is returned in the non-typechecked format expected by
        `parallel_check_hyps`.
        """
        self.log.info('started with %s goals' % len(self.goals))
        try:
            verdict = self.main_loop()
        except KeyboardInterrupt, e:
            self.log.error('interrupted by user')
            self.cancel_all_tasks()
            raise e
        self.print_task_pool()
        self.log.info('finished')
        return verdict
