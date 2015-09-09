This example target can be used to run the seL4 binary verification. It
assumes that the graph-refine repository has been placed along side the
l4v and HOL4 repositories, as will be the case if checked out as part of
the [NICTA verification manifest](https://github.com/seL4/verification-manifest).

The Makefile will invoke all the necessary steps, however, not all the tools
needed are provided, and some require additional configuration.

In particular:
  - Python is required. Any python2 installation should be compatible.
  - A cross compiler targeting 32-bit ARM is required.
    + e.g. to use `arm-linux-gnueabi-gcc`, set environment variable `TOOLPREFIX=arm-linux-gnueabi-`
    + gcc-4 series compilers are recommended for use with seL4.
    + non-gcc compilers may require `CONFIG_KERNEL_COMPILER=compiler-name`
  - An instance of binutils' `objdump` for 32-bit ARM is required
    + this tool should be named `"$TOOLPREFIX"-objdump`
  - Isabelle is provided but must be configured, see its README
    + the configuration requirements are the same as for the [L4.verified proofs](https://github.com/seL4/l4v)
    + the seL4 C model is built, which usually requires Isabelle in 64-bit mode ( `ML_PLATFORM="$ISABELLE_PLATFORM64"` in Isabelle's etc/settings )
  - HOL4 is provided but must be configured, see its README and INSTALL files.
    + HOL4 will require an ML environment, typically polyML.
    + the final `bin/build` step of installing HOL4 can be deferred (to save time) and will be run by the Makefile.
    + transient faults have sometimes been observed running the HOL4
decompiler. try rerunning the decompiler, or adjusting polyML version.
  - The standalone variant of the NICTA C parser must build
    + the parser is provided in the `l4v` directory
    + building the parser may require MLton installed, see the [L4.verified README.md](https://github.com/seL4/l4v)
  - Either one or two SMT solvers is required, and a .solverlist file must locate them.
    + the solver self-test `python ../solver.py test` will document the
.solverlist format, and check for solver compatibility if solvers are found.
    + the tool uses an online solver and an offline solver, with different requirements.
    + any SMTLIB2-compatible solver supporting the `QF_ABV` logic can be used,
and we have had success with Z3, CVC4, MathSAT5 and SONOLAR.
    + Using Z3 as the offline solver is not recommended, because of the way it
generates underspecified models for some array problems.
    + SONOLAR cannot be used as the online solver.
  - The proof process takes a long time, and some goals may time out.
    + the process typically takes around 10 hours, but this varies extensively
with SMT solver version and compiler version.
    + SONOLAR is the only solver known to solve all the problems created here
without timeouts, using other solvers will probably result in numerous timeouts.
    + timeouts are not fatal, they will be handled and summarised in the final report.


