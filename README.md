The NICTA Graph Refinement Toolset
==================================

This is a set of tools which discover and check refinement proofs between
programs with fairly arbitrary control flow graphs, including a number of
kinds of loop relationships. The tools are written in python and make heavy
use of SMT solvers.

The design and theory of this tool are described in the paper [Translation
Validation for a Verified OS Kernel][1] by Sewell, Myreen & Klein.

  [1]: https://ssrg.nicta.com.au/publications/nictaabstracts/Sewell_MK_13.abstract.pml "Translation Validation for a Verified OS Kernel"

Repository Setup
----------------

This tool can be used as it is. It is also designed to link with the
[L4.verified][2] proof chain. The full proof chain can be fetched via a
Google [repo][3] setup. To obtain the full environment, instead of cloning
this repository, follow the instructions in the [manifest repository][4] here:

   https://github.com/seL4/verification-manifest

To set up the various tools in the verification bundle, see the section
[Dependencies](#dependencies) below.

  [2]: https://github.com/seL4/l4v                   "L4.verified Repository"
  [3]: http://source.android.com/source/downloading.html#installing-repo     "google repo installation"
  [4]: https://github.com/seL4/verification-manifest "Verification Manifest Repository"

Examples
--------

The [`example`](example/) and [`loop-example`](loop-example/) directories
contain prebuilt example refinement targets. They can be used to exercise the
tool as follows:

    python graph-refine.py example quiet all
    python graph-refine.py loop-example/O1 report all

The [`seL4-example`](seL4-example/) directory contains a recipe for building
the seL4 binary verification problem. If this repository is set up via the
[verification manifest][4] then most of the necessary components will be
present. More information on running the full process is included in the
[`seL4-example`](seL4-example/) directory.

Dependencies
------------

The tool requires the use of an SMT solver supporting the QF\_ABV logic, which
is not provided here. Available solvers should be listed in a .solverlist
configuration file, which is described in [`solver.py`](solver.py). The tool
will also provide instructions on the command line if the configuration is
missing or invalid.

To test the solver setup is working:

    python solver.py test

Additional dependencies are required to run the full seL4 binary verification
problem. They are described in the [`seL4-example`](seL4-example/) directory.

Usage
-----

The tool is invoked by:

    python graph-refine.py <target> <instructions>

A target is a directory which contains all of the functions and configuration
associated with an input problem. Target directories must contain a target.py
setup script. See the example directory for an example.

There are various instructions available:

  - all: test all functions. this will usually be the last instruction.
  - no-loops: skip functions with loops
  - only-loops: skip functions without loops
  - quiet: suppress diagnostic output
  - report: report mode. suppress diagnostic output, but format a report on proof structure and progress.

Overview
--------

  - [syntax.py](syntax.py): defines the syntax of the graph language and its parser. A syntax reference is included.
  - [logic.py](logic.py): defines the top-level per-function proof obligations. Also provides various graph algorithms.
  - [problem.py](problem.py): stores the state of one refinement problem. Keeps mutable copies of graph functions, allowing inlining.
  - [solver.py](solver.py): controls the SMT solver. Manages an SMT problem state and some logical extensions.
  - [rep\_graph.py](rep_graph.py): populates the solver state with a model produced from a problem.
  - [check.py](check.py): defines the refinement proof format and the process for checking a proof.
  - [search.py](search.py): searches for a refinement proof.
  - [stack\_logic.py](stack_logic.py): provides additional analysis to address stack aspects of the binary calling convention.
  - [graph-refine.py](graph-refine.py): top level.

  - [trace\_refute.py](trace_refute.py): adaptation of this tool to detect
    impossible traces. This may be useful for other static analysis, e.g. WCET
    estimation.
  - [debug.py](debug.py): debug helper code.

