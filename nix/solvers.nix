# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Write a solver configuration (.solverlist) to the Nix store.

let

  inherit (import ./pins.nix) pkgs lib;
  sonolar_available = pkgs.system == "x86_64-linux";

in

# Optionally accept a solver config, which may override
# attributes in default_solver_config below.
{
  use_sonolar ? sonolar_available,
  solver_config ? {},
}:

let

  default_solver_list =
    if use_sonolar
    then [ "yices" "sonolar" "cvc4" ]
    else [ "yices" "cvc4" ];

  default_solver_config = {
    online_solver = "cvc4";
    offline_solver = if use_sonolar then "sonolar" else "cvc4";
    strategy_solvers = default_solver_list;
    model_solvers = default_solver_list;
  };

  # Fill in missing solver_config items using defaults.
  solver_config_with_defaults = with builtins;
    let
      # Ensure solver_config has no unwanted items.
      bad_attrs = filter (n: !hasAttr n default_solver_config) (attrNames solver_config);
      checked_config = if bad_attrs == []
        then solver_config
        else throw "solvers.nix: solver_config has unwanted attributes: ${toString bad_attrs}";
    in default_solver_config // checked_config;

in

with solver_config_with_defaults;

let

  maybe_sonolar =  if !sonolar_available then {} else {
    sonolar = rec {
      pkg = pkgs.fetchzip rec {
        name = "sonolar-2014-12-04";
        url = "http://www.informatik.uni-bremen.de/agbs/florian/sonolar/${name}-x86_64-linux.tar.gz";
        sha256 = "sha256:01k6270ycv532w5hx0xhfms63migr7wq359lsnr4a6d047q15ix7";
      };
      offline = "${pkg}/bin/sonolar --input-format=smtlib2";
    };
  };

  solver_cmds = maybe_sonolar // {
    cvc4 = rec {
      pkg = pkgs.cvc4;
      online = "${pkg}/bin/cvc4 --incremental --lang smt --tlimit=120";
      offline = "${pkg}/bin/cvc4 --lang smt";
    };
    yices = rec {
      pkg = pkgs.yices;
      offline = "${pkg}/bin/yices-smt2";
    };
  };

  # Names of selected solvers for each mode. May contain duplicates.
  selected_solvers = {
    offline = [ offline_solver ] ++ strategy_solvers ++ model_solvers;
    online = [ online_solver ];
  };

  # Solver packages selected by solver_config.
  solvers = with lib;
    mapAttrs (_: s: s.pkg) (getAttrs (concatLists (attrValues selected_solvers)) solver_cmds);

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

  # We currently always use both "all" and "hyp" strategies,
  # and both machine-word- and byte-granular views of memory.
  strategy =
    let f = n: "${n} all, ${n} hyp, ${n}-word8 all, ${n}-word8 hyp";
    in lib.concatMapStringsSep ", " f strategy_solvers;

  # For model repair, first use all selected solvers with a machine-word-granular
  # view of memory, then use the selected solvers with a byte-granular view.
  model_strategy = with lib;
    let solv_suf = suf: map (solv: solv + suf) model_solvers;
    in concatStringsSep ", " (concatMap solv_suf ["" "-word8"]);

  # Render the solverlist templates for the given mode and selected solvers,
  # returning a list of unterminated lines.
  render_solvers_mode = mode: selected: with lib;
    concatLists (mapAttrsToList (name: cmd: mk_solvers."${mode}" name cmd.${mode})
                                (getAttrs selected solver_cmds));

  # Render solverlist templates for both modes, emitting online templates first.
  selected_solver_configs = with lib;
    concatStringsSep "\n"
      (concatLists (attrVals [ "online" "offline" ]
                             (mapAttrs render_solvers_mode selected_solvers)));

  # The solver configuration file.
  solverlist = pkgs.writeTextFile {
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
