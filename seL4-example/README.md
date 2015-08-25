This example target can be used to run the seL4 binary verification. It
assumes that the graph-refine repository has been placed along side the
l4v and HOL4 repositories, as will be the case if checked out as part of
the NICTA verification manifest (see github.com/seL4/verification-manifest ).

The Makefile will invoke all the necessary steps, however, not all the tools
needed are provided, and some require more configuration.

In particular:
  - a python environment is required.
  - a cross compiler targeting 32-bit ARM is required, and CC/TOOLPREFIX in the
    Makefile must be adjusted to locate it.
  - an instance of 'objdump' for 32-bit ARM is required, and TOOLPREFIX in the
    Makefile must be adjusted to locate it.
  - isabelle is provided but must be configured, see its README
  - HOL4 is provided but must be configured, see its README/INSTALL
    + HOL4 will require an ML environment installed
  - the standalone variant of the C parser must build
    + installing mlton may solve some problems with this
  - an SMT solver (e.g. Z3, CVC4) is required, and a .solverlist file must
    locate it. graph-refine will provide instructions when executed.



