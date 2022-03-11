# Copyright (c) 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

# Write a solver configuration (.solverlist) to the Nix store.

{
  pkgs ? import <nixpkgs> {},
  solver_config ? {},
}:

with pkgs;
with lib;

with (import ./util.nix { inherit pkgs; });

# Fill in default values for solver_config.
with ({ online_solver ? "cvc4",
        offline_solver ? "sonolar",
        strategy_solvers ? [ "yices" "sonolar" "cvc4" ],
        model_solvers ? [ "yices" "sonolar" "cvc4" ] }:
      { inherit online_solver offline_solver strategy_solvers model_solvers; })
     solver_config;

let

  sonolar = fetchzip {
    name = "sonolar";
    url = "http://www.informatik.uni-bremen.de/agbs/florian/sonolar/sonolar-2014-12-04-x86_64-linux.tar.gz";
    sha256 = "sha256-p8cS8CGgGUWy1TSVgfnJL9ZhdHWwgw4LF6Ns5sERZgY=";
  };

  # Available solver packages.
  solver_pkgs = { inherit cvc4 sonolar yices; };

  # Names of selected solvers for each mode. May contain duplicates.
  selected_solvers = {
    offline = [ offline_solver ] ++ strategy_solvers ++ model_solvers;
    online = [ online_solver ];
  };

  # Solver packages selected by solver_config.
  solvers = getAttrs (concatLists (attrValues selected_solvers)) solver_pkgs;

  # Command-lines for solvers in offline and online modes.
  solver_cmds = {
    offline = {
      cvc4 = "${cvc4}/bin/cvc4 --lang smt";
      sonolar = "${sonolar}/bin/sonolar --input-format=smtlib2";
      yices = "${yices}/bin/yices-smt2";
    };
    online = {
      cvc4 = "${cvc4}/bin/cvc4 --incremental --lang smt --tlimit=120";
    };
  };

  # Templates for solverlist solver specifications, in offline and online modes.
  mk_solvers = {
    offline = name: cmd: [
      "${name}: offline:: ${cmd}"
      "${name}-word8: offline: mem_mode=8: ${cmd}"
    ];
    online = name: cmd: [
      "${name}: online:: ${cmd}"
    ];
  };

  # Render the solverlist templates for the given mode and selected solvers,
  # returning a list of unterminated lines.
  render_solvers_mode = mode: selected:
    concatMapAttrs mk_solvers."${mode}" (getAttrs selected solver_cmds."${mode}");

  # Render solverlist templates for both modes, emitting online templates first.
  render_solvers = modes:
    concatLists (attrVals [ "online" "offline" ] (mapAttrs render_solvers_mode modes));

  # We currently always use both "all" and "hyp" strategies,
  # and both machine-word- and byte-granular views of memory.
  strategy =
    let f = n: "${n} all, ${n} hyp, ${n}-word8 all, ${n}-word8 hyp";
    in concatMapStringsSep ", " f strategy_solvers;

  # For model repair, first use all selected solvers with a machine-word-granular
  # view of memory, then use the selected solvers with a byte-granular view.
  model_strategy =
    let solv_suf = suf: map (solv: solv + suf) model_solvers;
    in concatStringsSep ", " (concatMap solv_suf ["" "-word8"]);

  # Rendered solver templates for all selected solvers.
  selected_solver_configs = concatStringsSep "\n" (render_solvers selected_solvers);

  # The solver configuration file.
  solverlist = writeTextFile {
    name = "graph-refine-solverlist";
    destination = "/.solverlist";
    text = ''
      strategy: ${strategy}
      model-strategy: ${model_strategy}
      online-solver: ${online_solver}
      offline-solver: ${offline_solver}
      ${selected_solver_configs}
    '';
  };

in { inherit solverlist solvers; }
