# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Packages graph-refine and a solver configuration as a Nix derivation,
# and also produces a Docker image.

{ solver_config ? {} }:

let

  inherit (import ./pins.nix) pkgs python_2_7_pkgs lib stdenv;
  inherit (import ./util.nix) explicit_sources;

  solvers = import ./solvers.nix { inherit solver_config; };

  graph-refine-python =  python_2_7_pkgs.python2.withPackages (python-pkgs: with python-pkgs; [
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
  graph-refine-py = with lib;
    let
      modules = toString graph-refine-modules;
      py = stdenv.mkDerivation rec {
        name = "graph-refine-py";
        src = explicit_sources "graph-refine-sources" ./.. graph-refine-modules;
        installPhase = ''
          mkdir -p $out
          (cd $src && tar cf - ${modules}) | (cd $out && tar xf -)
          (cd $out && ${graph-refine-python.interpreter} -m compileall ${modules})
        '';
      };
    in py;

  # Wrapper that sets environment variables for graph-refine.
  # We use runCommand instead of writeScriptBin so we can grab the store path from `$out`.
  graph-refine =
    let
      text = ''
        #!${pkgs.runtimeShell}
        set -euo pipefail
        export GRAPH_REFINE_SOLVERLIST_DIR="${solvers.solverlist}"
        export GRAPH_REFINE_VERSION_INFO="NIX_STORE_PATH NIX_GRAPH_REFINE_OUTPUT_DIR"
        exec "${graph-refine-python.interpreter}" "${graph-refine-py}/graph-refine.py" "$@"
      '';
      deriv_args = { inherit text; passAsFile = [ "text" ]; nativeBuildInputs = [pkgs.perl]; };
      script = pkgs.runCommand "graph-refine" deriv_args ''
        mkdir -p "$out/bin"
        out_dir="$(basename "$out")"
        perl -pe "s/\bNIX_GRAPH_REFINE_OUTPUT_DIR\b/$out_dir/" "$textPath" > "$out/bin/graph-refine"
        chmod +x "$out/bin/graph-refine"
      '';
    in script;

  # A graph-refine Docker image.
  graph-refine-image = with pkgs; dockerTools.streamLayeredImage {
    name = "graph-refine";
    contents = [ bashInteractive coreutils graph-refine graph-refine-python ];
    config = { Entrypoint = [ "${graph-refine}/bin/graph-refine" ]; };
  };

  graph-refine-runner-py = with pkgs; runCommand "graph-refine-runner-py" {} ''
    mkdir -p "$out"
    cp --preserve=all "${../ci/runner.py}" "$out/graph-refine-runner.py"
    (cd "$out" && "${python3.interpreter}" -m compileall "graph-refine-runner.py")
  '';

  graph-refine-runner = with pkgs; writeScriptBin "graph-refine-runner" ''
    #!${runtimeShell}
    export GRAPH_REFINE_SCRIPT="${graph-refine}/bin/graph-refine"
    exec "${python3.interpreter}" "${graph-refine-runner-py}/graph-refine-runner.py" "$@"
  '';

  graph-refine-runner-image = with pkgs; dockerTools.streamLayeredImage {
    name = "graph-refine-runner";
    contents = [
      bashInteractive coreutils
      graph-refine graph-refine-runner
      graph-refine-python python3
      sqlite
    ];
    config = { Entrypoint = [ "${graph-refine-runner}/bin/graph-refine-runner" ]; };
  };

in {

  inherit
    graph-refine
    graph-refine-image
    graph-refine-runner
    graph-refine-runner-image
    graph-refine-python;

  inherit (solvers)
    solverlist
    solvers;

}
