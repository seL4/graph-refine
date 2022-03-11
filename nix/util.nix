# Copyright (c) 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

{ pkgs ? import <nixpkgs> {} }:

with pkgs;
with lib;

rec {

  # Map a function over an attribute set, concatenating the resulting lists.
  concatMapAttrs = f: set: concatLists (mapAttrsToList f set);

  # Generate an attribute set from a list,
  # given functions for generating attribute names and values.
  genAttrs' = f: g: xs:
    listToAttrs (map (x: nameValuePair (f x) (g x)) xs);

  # Prepend all directory prefixes to a list of file paths.
  # This is useful for filtering sources using an explicit list of files
  # that may be in subdirectories.
  paths_with_dir_prefixes = paths:
    let xs = genericClosure { startSet = map (p: { key = p; }) (reverseList paths);
                              operator = { key }: let d = dirOf key;
                                                      s = { key = d; };
                                                  in if d == "." then [] else [s]; };
    in reverseList (map (x: x.key) xs);

  # Build a set of absolute paths from a list of relative paths.
  paths_absolute = root_path: genAttrs' (p: root_path + p) (p: p);

  # A filter for use with `cleanSourceWith`, that ignores roughly the
  # same paths as .gitignore files.
  gitignoreFilter =
    let
      gitignore_src = pkgs.fetchFromGitHub {
        owner = "hercules-ci";
        repo = "gitignore.nix";
        rev = "5b9e0ff9d3b551234b4f3eb3983744fa354b17f1";
        sha256 = "sha256-o/BdVjNwcB6jOmzZjOH703BesSkkS5O7ej3xhyO8hAY=";
      };
    in (import gitignore_src { inherit lib; }).gitignoreFilter;

}
