# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: MIT

{ solver_config ? {} }:

let

  inherit (import nix/pins.nix) pkgs rosetta-pkgs;
  inherit (import nix/sel4-deps.nix) sel4-deps;
  inherit (import nix/l4v-deps.nix) l4v-deps;

  inherit (import nix/graph-refine.nix { inherit solver_config; })
    graph-refine-python solvers solverlist;

  graph-refine-deps = [
    graph-refine-python
    rosetta-pkgs.mlton
    solverlist
  ];

in pkgs.mkShell {
  packages = sel4-deps ++ l4v-deps ++ graph-refine-deps ++ builtins.attrValues solvers;
  GRAPH_REFINE_SOLVERLIST_DIR = solverlist;
}
