<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

The Graph-To-Graph WCET Toolset
====================
Building on the Data 61 Graph Refinement toolset, this tool estimates the Worst Case Execution Time of conforming C code.

Dependencies
----------
You will need an operational setup of the graph-refine toolset, follow the instructions on:
https://github.com/seL4-projects/graph-refine

We have tested SONOLAR
(http://www.informatik.uni-bremen.de/agbs/florian/sonolar/) and
CVC4(http://cvc4.cs.nyu.edu/downloads/) and for this setup. The specific
versions we used were SONOLAR-2014-12-04, CVC4-1.4.

Refer to graph-refine/seL4-example/README.md for details.
We have tested with this following .solverlist setup:

---

SONOLAR: offline : (path to sonolar dir/bin/sonolar) --input-format=smtlib2
CVC4: online: (path to the cvc4-1.4 binary) --incremental --lang smt -tlimit=5000

---

*NUS Chronos*

The toolchain expects our modified version of the NUS Chronos WCET toolchain (http://www.comp.nus.edu.sg/~rpembed/chronos/) to live at (verification)/chronos4.2/
Which is avaliable via:

`git clone https://github.com/seL4-projects/chronos4.2`
`cd chronos4.2`
`make`

*IBM Cplex 12.6.0.0*

CPLEX can be obtained, free of charge, under the IBM Academic Initiative for qualifying academics.
Use the exact version, 12.6.2 in particualr is incompatible with graph\_to\_graph.

A JRE bugs may crashes the launcher for any but extremely short prompt name, you can work around it with:
`PS1= ./cplex_studio126.linux-x86-64.bin`

Then add cplex to your path.

Setting up graph-refine
---------
The graph-to-graph directory needs to contain a symbolic link named graph\_refine to the top level directory so it can import its modules:

    `ln --symbolic ../ graph_refine`

    Your setup should look like this:
    verification/
        chronos4.2
        graph-refine
            __init__.py (blank file)
            .solverlist
            graph_to_graph/
                graph_refine (symbolic link to parent directory)

Using the toolset to estimate WCET
--------
To estimate the WCET of a target with dummy loopheads:

Firstly generate the dummy loop counts with

`python graph_to_graph.py targetDirectory entryFunction --l`

this generates loop\_counts.py under the target directory with dummy loop counts.

then invoke

`python graph_to_graph.py targetDirectory entryFunction --L`
to generate an ILP problem with the loop counts in targetDirectory/loop\_counts.pyand solve it with chronos.

The toolset can also automatically determine loop bounds, to do this firstly generate the loopheads (and dummy loop bounds) with the --l flag, then execute:

`python convert_loop_bounds.py targetDirectory`

to automatically determine all loop bounds. Note this can take hours depending on the target. The derived results may be manually overwritten by editing loop\_counts.py

Finally use the automatically deduced loopbounds to estimate the WCET with:

`python graph_to_graph.py targetDirectory entryFunction --L`

The resulting estimated WCET is only usable if the loop\_counts.py file contains no dummy entry. If it does and the user knows the loop bounds, they can be manually annotatedby modifying the loop\_counts.py file.

Infeasible paths elimination
--------

Firstly, we strip the footer off the .ilp file with automatically annotated loop bounds that we got when we ran graph\_to\_graphy.py with the --L flag.

`python cplex.py targetDirectory/handleSyscall.imm.ilp --f `

We can then instructs conflict.py to produce the first round of candidate infeasible paths with blank conflict files. conflicty.py accepts two conflict file so that a manual file can be used in addition to an automatically produced one.
'python conflict.py targetDirectory/handleSyscall.imm.map blank\_file blank\_file targetDirectory/handleSyscall.imm'

Using the toolset on seL4
--------
You can refer to sel4.systems on how to get a cross compiler (required by graph\_refine).
cd into the seL4-example directory and build it (see graph-refine for instructions).

seL4 contains loops that are only bounded by preemption points, and the
apparatus cannot determine the bounds for those loops. Thus the loop\_counts.py
file (under the target directory) will contains dummy loop bounds. The
preemption annotations, which is part of the infeaisble paths elimination
process will resolve them properly. This means when we invoke
graph\_to\_graph.py Cplex will return a unrealistically large number, that's
expected. All we need from it is the .ilp file.

Using handleSyscall as the entry function:

1. Generate the loop bounds file with dummy loop counts
    `python graph_to_graph.py ../seL4-example handleSyscall --l`
2. Automatically deduce the loop bounds with
    `python convert_loop_bounds.py seL4-exapmle `
3. Generate the ILP file with theese automatically derived loop bounds, disregard the resulting WCET, because the loop bounds file contain
    `python graph_to_graph.py ../seL4-example handleSyscall --L`
4. Strip the ilp file of its footer
    `python cplex.py ../seL4-example/handleSyscall.imm.ilp --f`
5. Invoke conflict.py to produce an annotated ilp files with the preemption points and run cplex on it
    `python conflict.py ../seL4-example/handleSyscall.imm.map blank\_file ../seL4-example/refutes_manual_open_sys.txt ../seL4-example/handleSyscall.imm.ilp_nofooter newIlp.ilp ../seL4-example --cx 5 new.sol`

    Graph to graph also provides an automated shorthand for carrying out the above five steps:
    `python graph_to_graph.py ../seL4-example handleSyscall --x ../seL4-example ../seL4-example/refutes_manual_open_sys.txt`

seL4-example/refutes\_manual\_open\_sys.txt should contains, and mark the binary loops that are bounded only by phantom preemption points. These are the loops in cancelAllIPC, cancelAllSignals and cancelBadgeSends. The format is:
`[loop address (refer to the generated loop\_counts.py)]:phantom_preemp_point`

Overview
--------

 - [addr\_utils.py](addr\_utils.py): Miscellanous utility functions
 - [bench.py](bench.py): Ties the WCET estimation tools together, also contains utilities for debugging CFG conversions.
 - [convert\_loop\_bounds.py](elf\_parser.py): Interfaces with graph-refine's loop\_bounds.py and stores its results in targetDirectory/loop\_counts.py
 - [cplex.py](cplex.py): Utility functions for interfacing with the CPLEX solver
 - [elf\_correlate.py](elf\_correlate.py): Defines the immFunction format and uses it to translate a graph-refine function, and all the function that it calls into a Control Flow Graph (CFG)

 - [elf\_parser.py](elf\_file.py): Various (text dumped) elf file parsing utility functions
 - [reconstruct.py](reconstruct.py): Reconstruct the worst case from a ILP solution.
 - [conflict.py](conflict.py): Annotate a given ILP problem with trace\_refute and artificial/phantom preemption points.
 - [auto\_infea.py](auto\_infea.py): Repeatedly and automatically eliminate infeasible paths
 - [graph\_to\_graph.py](graph\_to\_graph.py): The command line interface to graph\_to\_graph.
 - [dot\_utils.py](dot\_utils.py): Visualize function graphs, used to debug CFG conversion. It's outdated and requires rewritings.
 - [py\_dot.py](py\_dot.py): A direct copy of Graphviz's dot language Python interface. It's distributed under the MIT license.
 - [chronos/parser.py](chronos/parser.py): An single instruction parser used to emit the IMM file that chronos accepts
 - [chronos/emitter.py](chronos/emitter.py): Our interface to Chronos, generates a CFG in Chronos's IMM format from an immFunction


Files in a Target directory
--------
 - [loop\_counts.py]: Generated by graph\_to\_graph, you can manually enter the loop bounds to this file after that. Automatical loop bounds discovery will update this file too.
                      this is recorded as  a dictionary named loops_by_fs of function to dictionaries of binary loop head address to a triple (bound, comment, worker_id).
                      If the comment contains the keyword ignored, convert_loop_bounds.py will not search for its bound. The worker_id is used for a undocumented parallesation scheme, and should be ignored and preserved by the user.
 - [entryFunctionName.imm]: input to Chronos
 - [entryFunctionName.imm.ilp]: ilp file generated by Chronos
 - [entryFunctionName.imm.map]: Describes how the block ids in the .ilp file maps to the binary addresses.
 - [phantom\_preempt.py]: Manual annotations that direct graph\_to\_graph to inject phantom preemption points into functions inside the target. Renders the result unsound, can only used for debugging purposes.


