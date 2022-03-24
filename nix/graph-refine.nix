# Copyright (c) 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

# Packages graph-refine and a solver configuration as a Nix derivation,
# and also produces a Docker image.

{
  pkgs ? import <nixpkgs> {},
  solver_config ? {},
  graph_refine_srcs ? { RISCV64 = ../.; },
}:

with pkgs;
with lib;
with stdenv;

with (import ./util.nix { inherit pkgs; });
with (import ./solvers.nix { inherit pkgs solver_config; });

let

  graph-refine-python = python2.withPackages (python-pkgs: with python-pkgs; [
    enum34 typing psutil
  ]);

  # List of graph-refine Python source files.
  # We take only the files we need, to minimise Docker layer churn.
  graph-refine-modules = [
    "c_rodata.py"
    "check.py"
    "graph-refine.py"
    "inst_logic.py"
    "logic.py"
    "loop_bounds.py"
    "objdump.py"
    "parallel_solver.py"
    "problem.py"
    "pseudo_compile.py"
    "rep_graph.py"
    "search.py"
    "solver.py"
    "stack_logic.py"
    "stats.py"
    "syntax.py"
    "target_objects.py"
    "trace_refute.py"
    "typed_commons.py"
  ];

  # Byte-code-compiled Python sources.
  # Parameterised by architecture and source location, so that we can use
  # different implementations for different architectures.
  graph-refine-py = arch: src:
    let
      paths = paths_absolute (toString src + "/") (paths_with_dir_prefixes graph-refine-modules);
      arch_suffix = name: name + "-" + arch;
      srcs = cleanSourceWith rec {
        name = arch_suffix "graph-refine-sources";
        inherit src;
        filter = path: type: hasAttr (toString path) paths;
      };
      py = mkDerivation rec {
        name = arch_suffix "graph-refine-py";
        src = srcs;
        installPhase = ''
          mkdir -p $out
          (cd $src && cp --preserve=all *py $out)
          (cd $out && ${graph-refine-python.interpreter} -m compileall *.py)
        '';
      };
    in py;

  # Wrapper that dispatches to the graph-refine version indicated
  # by the L4V_ARCH environment variable, and also passes additional
  # environment variables to graph-refine.
  # We use runCommand instead of writeScriptBin so we can grab the
  # store path from `$out`.
  graph-refine =
    let
      case = arch: src: "\"${arch}\") GRAPH_REFINE_PY=\"${graph-refine-py arch src}\";;";
      cmd = ''
        mkdir -p "$out/bin"
        cat > "$out/bin/graph-refine" <<EOF
        #!${runtimeShell}
        case "\$L4V_ARCH" in
          ${concatStringsSep "\n  " (mapAttrsToList case graph_refine_srcs)}
          "") echo "error: graph-refine: L4V_ARCH was not set" >&2 && exit 1;;
          *) echo "error: graph-refine: unsupported L4V_ARCH \"\$L4V_ARCH\"" >&2 && exit 1;;
        esac
        export GRAPH_REFINE_SOLVERLIST_DIR="${solverlist}"
        export GRAPH_REFINE_VERSION_INFO="NIX_STORE_PATH $(basename $out)"
        exec "${graph-refine-python.interpreter}" "\$GRAPH_REFINE_PY/graph-refine.py" "\$@"
        EOF
        chmod +x "$out/bin/graph-refine"
      '';
    in runCommand "graph-refine" {} cmd;

  # A graph-refine Docker image.
  graph-refine-image = dockerTools.streamLayeredImage {
    name = "graph-refine";
    contents = [ bashInteractive coreutils graph-refine graph-refine-python ];
    config = { Entrypoint = "${graph-refine}/bin/graph-refine"; };
  };

  graph-refine-parallel-py = runCommand "graph-refine-parallel-py" {} ''
    mkdir -p "$out"
    cp --preserve=all "${../queue/worker.py}" "$out/graph-refine-parallel.py"
    (cd "$out" && "${python3.interpreter}" -m compileall "graph-refine-parallel.py")
  '';

  graph-refine-parallel = writeScriptBin "graph-refine-parallel" ''
    #!${runtimeShell}
    export GRAPH_REFINE_SCRIPT="${graph-refine}/bin/graph-refine"
    exec "${python3.interpreter}" "${graph-refine-parallel-py}/graph-refine-parallel.py" "$@"
  '';

  graph-refine-parallel-image = dockerTools.streamLayeredImage {
    name = "graph-refine-parallel";
    contents = [
      bashInteractive coreutils
      graph-refine graph-refine-parallel
      graph-refine-python python3
    ];
    config = { Entrypoint = "${graph-refine-parallel}/bin/graph-refine-parallel"; };
  };

in {
  inherit
    graph-refine
    graph-refine-image
    graph-refine-parallel
    graph-refine-parallel-image
    graph-refine-python
    solverlist
    solvers;
}
