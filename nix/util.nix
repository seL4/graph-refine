# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Shared utility functions.

let

  inherit (import ./pins.nix) pkgs lib;

in

rec {

  # Like nixpkgs fetchFromGitHub, but using the built-in fetchTarball.
  fetchGitHub = { owner, repo, rev, name ? "${owner}-${repo}-${rev}", sha256 }:
    fetchTarball {
      inherit name sha256;
      url = "https://github.com/${owner}/${repo}/archive/${rev}.tar.gz";
    };

  # Fetch and import a pinned nixpkgs.
  fetch-nixpkgs = { rev, sha256 }: import (fetchGitHub {
    owner = "nixos"; repo = "nixpkgs"; name = "nixpkgs";
    inherit rev sha256;
  });

  # Some packages don't work natively on Apple Silicon, but work with Rosetta 2.
  mk-rosetta-pkgs = pkgs: mk-pkgs: config:
    mk-pkgs (if pkgs.system == "aarch64-darwin"
             then { localSystem = pkgs.lib.systems.examples.x86_64-darwin; } // config
             else config);

  # A source filter that accepts an explicit list of paths relative to a given root.
  explicit_sources_filter = root: paths:
    assert (builtins.isPath root);
    with lib;
    let
      # Augment the list of paths with all of its own ancestor paths.
      # E.g. [ "x/y/z" "a/b/c" ] -> [ "x" "a" "x/y" "a/b" "x/y/z" "a/b/c" ]
      # This is necessary if the paths contains files in subdirectories,
      # since source filtering will not descend into directories that do not
      # themselves pass the filter.
      prefix_paths =
        let xs = genericClosure { startSet = map (p: { key = p; }) paths;
                                  operator = { key }: let d = builtins.dirOf key;
                                                          s = { key = d; };
                                                      in if d == "." then [] else [s]; };
        in map (x: x.key) xs;

      abs_path = path: toString (root + "/${path}");
      prefix_path_set = listToAttrs (map (p: nameValuePair (abs_path p) null) prefix_paths);
      abs_paths = map abs_path paths;
      is_desc_path = desc: builtins.any (anc: lib.hasPrefix "${anc}/" desc) abs_paths;

      filter = path: type:
        let p = toString path; in hasAttr p prefix_path_set || is_desc_path p;

    in filter;

  explicit_sources = name: src: paths: lib.cleanSourceWith {
    inherit name src;
    filter = explicit_sources_filter src paths;
  };

  # A conjunction of two-place predicates. Can be used with path filters.
  conj2 = preds: x: y: builtins.all (pred: pred x y) preds;

  # A conjunction of two-place predicates. Can be used with path filters.
  disj2 = preds: x: y: builtins.any (pred: pred x y) preds;

  # Apply a function to an attribute value,
  # with a default if the attribute is not present.
  maybeGetAttr = name: set: default: f:
    if lib.hasAttr name set then f set.${name} else default;

  # Creates a shell script snippet that checks for the presence of given
  # environment variables, and prints a usage message if not.
  mk-check-env = { name, env }:
    let
      env-checks = map (var: ''[ -z ''${${var}+x} ]'') (lib.attrNames env);
      choices-check = var: info:
        let
          check = c: ''[ "''${${var}}" != "${c}" ]'';
          checks = cs: ''
            if ${lib.concatStringsSep " && " (map check cs)}; then
              echo "${name}: error: invalid value for environment variable ${var}" >&2
              echo "${name}: valid choices for ${var}: ${lib.concatStringsSep " " cs}" >&2
              exit 1
            fi
          '';
        in maybeGetAttr "choices" info "" (cs: lib.removeSuffix "\n" (checks cs));
      choices-checks =
        lib.concatStringsSep "\n" (lib.mapAttrsToList choices-check env);
      var-usage = var: info:
        let
          choices = maybeGetAttr "choices" info []
            (cs: ["one of: ${lib.concatStringsSep " " cs}"]);
          help_ls = maybeGetAttr "help" info [] (h: [h]);
          help = lib.concatStringsSep " - " ([var] ++ help_ls ++ choices);
        in ''echo "  ${help}" >&2'';
      exists-check = ''
        if ${lib.concatStringsSep " || " env-checks}; then
          echo "${name}: error: required environment variables not set" >&2
          echo "${name}: required variables:" >&2
          ${lib.concatStringsSep "\n  " (lib.mapAttrsToList var-usage env)}
          exit 1
        fi
      '';
    in lib.removeSuffix "\n" (exists-check + choices-checks);

}
