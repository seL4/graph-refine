# Copyright (c) 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

# Packages graph-refine and a solver configuration as a Nix derivation,
# and also produces a Docker image.

{
  pkgs ? import <nixpkgs> {},
  solver_config ? {},
  graph_refine_src ? ../.,
  image_name ? "graph-refine",
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

  # Sources added to Nix store.
  graph-refine-sources =
    let
      src = graph_refine_src;
      paths = paths_absolute (toString src + "/") (paths_with_dir_prefixes graph-refine-modules);
      srcs = cleanSourceWith rec {
        name = "graph-refine-sources";
        inherit src;
        filter = path: type: hasAttr (toString path) paths;
      };
    in srcs;

  # Byte-code-compiled Python sources.
  graph-refine-py = mkDerivation rec {
    name = "graph-refine-py";
    src = graph-refine-sources;
    modules = concatStringsSep " " graph-refine-modules;
    installPhase = ''
      mkdir -p $out
      (cd $src && cp --preserve=all $modules $out)
      (cd $out && ${graph-refine-python.interpreter} -m compileall $modules)
    '';
  };

  # Wrapper that passes environment variables to graph-refine.
  # We use runCommand instead of writeShellScriptBin so we can grab the
  # store path from `$out`.
  graph-refine = runCommand "graph-refine" {} ''
    mkdir -p "$out/bin"
    cat > "$out/bin/graph-refine" <<EOF
    #!${runtimeShell}
    export GRAPH_REFINE_SOLVERLIST_DIR="${solverlist}"
    export GRAPH_REFINE_VERSION_INFO="NIX_STORE_PATH $(basename $out)"
    exec "${graph-refine-python.interpreter}" "${graph-refine-py}/graph-refine.py" "\$@"
    EOF
    chmod +x "$out/bin/graph-refine"
  '';

  # A graph-refine Docker image.
  graph-refine-image = dockerTools.streamLayeredImage {
    name = image_name;
    contents = [ bashInteractive coreutils graph-refine-python ];
    config = { Entrypoint = "${graph-refine}/bin/graph-refine"; };
  };

in { inherit graph-refine graph-refine-image graph-refine-python solverlist solvers; }
