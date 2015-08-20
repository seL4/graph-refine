This is the NICTA Graph Refinement toolset.

This is a set of tools, mostly written in python, to discover and check
refinement proofs between programs expressed in a particular graph language.
The graph language syntax and semantics are described here.

The tool requires the use of an SMT solver supporting the QF\_ABV logic, which
is not provided here. The tool will provide configuration instructions on its
first execution.

The design and theory of this tool are described in the paper "Translation
Validation for a Verified OS Kernel" by Sewell, Myreen & Klein.

Graph refinement process usage:

python graph-refine.py <target> <instructions>

Here <target> is a target directory, which specifies an input problem. It must
contain a target.py setup script. See the example directory for an example.

There are various instructions available:

  <name of function>: run checks for this function
  "all": run checks for all functions
  "no-loops": skip functions with loops
  "only-loops": skip functions without loops
  "quiet": quiet mode, only report progress.
  "report": report mode, produce a nice report on proof structure & progress.

The sources and the above-mentioned paper may be useful in understanding what
the proof process does.


