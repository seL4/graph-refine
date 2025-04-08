# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Pin versions of nixpkgs and other repositories used for building
# graph-refine, the decompiler, etc.

let

  inherit (import ./util.nix) fetchGitHub fetch-nixpkgs mk-rosetta-pkgs;

in

rec {

  # Recent nixpkgs pin used for most things.
  mk-default-pkgs = fetch-nixpkgs {
    # nixos-unstable 2023-01-13
    rev = "befc83905c965adfd33e5cae49acb0351f6e0404";
    sha256 = "sha256:0m0ik7z06q3rshhhrg2p0vsrkf2jnqcq5gq1q6wb9g291rhyk6h2";
  };

  # Python 2.7 needs an older pin.
  python_2_7_pkgs = fetch-nixpkgs {
    # nixos-unstable 2022-05-31
    rev = "d4964be44cb430760b266f5df34a185f2920e80e";
    sha256 = "sha256:01wd40yn8crz1dmypd9vcc9gcv8d83haai2cdv704vg2s423gg88";
  } {};

  # The arm-none-eabi cross compiler needs an older pin,
  # and on aarch64-darwin, only builds via Rosetta.
  mk-arm-cross-pkgs = mk-rosetta-pkgs pkgs (fetch-nixpkgs {
    # nixos-22.05 2023-01-13
    rev = "9e96b1562d67a90ca2f7cfb919f1e86b76a65a2c";
    sha256 = "sha256:0nma745rx2f2syggzl99r0mv1pmdy36nsar1wxggci647gdqriwf";
  });

  pkgs = mk-default-pkgs {};
  inherit (pkgs) lib stdenv;

  rosetta-pkgs = mk-rosetta-pkgs pkgs mk-default-pkgs {};

  herculesGitignore = import (fetchGitHub {
    owner = "hercules-ci";
    repo = "gitignore.nix";
    rev = "a20de23b925fd8264fd7fad6454652e142fd7f73";
    sha256 = "sha256:07vg2i9va38zbld9abs9lzqblz193vc5wvqd6h7amkmwf66ljcgh";
  }) { inherit lib; };

}
