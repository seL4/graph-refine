This example target can be used to run the seL4 binary verification. It
assumes that the graph-refine repository has been placed along side the
l4v and HOL4 repositories, as will be the case if checked out as part of
the NICTA verification manifest (see github.com/seL4/verification-manifest ).

The Makefile will invoke all the necessary steps, however, not all the tools
needed are provided, and some require more configuration.

In particular:
  - a python environment is required.
  - a cross compiler targeting 32-bit ARM is required.
    + e.g. to use `arm-linux-gnueabi-gcc`, set environment variable `TOOLPREFIX=arm-linux-gnueabi-`
    + gcc-4 series compilers are recommended for use with seL4.
    + non-gcc compilers may require CONFIG\_KERNEL\_COMPILER=compiler-name
  - an instance of 'objdump' for 32-bit ARM is required
    + this tool should be named `TOOLPREFIX-objdump`
  - isabelle is provided but must be configured, see its README
    + the configuration requirements are the same as for the [L4.verified proofs](https://github.com/seL4/l4v)
    + the seL4 C model is built, which usually requires Isabelle in 64-bit mode ( `ML\_PLATFORM="$ISABELLE\_PLATFORM64"` in Isabelle's etc/settings )
  - HOL4 is provided but must be configured, see its README/INSTALL
    + HOL4 will require an ML environment, i.e. polyml
  - the standalone variant of the C parser must build
    + this may require MLton installed, see the [L4.verified README.md](https://github.com/seL4/l4v)
  - an SMT solver (e.g. Z3, CVC4) is required, and a .solverlist file must
    locate it. graph-refine will provide instructions when executed.



