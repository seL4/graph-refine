# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Additional dependencies for running l4v proofs.

let

  inherit (import ./pins.nix) pkgs;

  l4v-texlive = with pkgs.texlive; combine {
    inherit
      collection-latexextra
      collection-fontsrecommended
      collection-metapost
      collection-bibtexextra;
  };

  l4v-deps = with pkgs; [
    l4v-texlive
  ];

in { inherit l4v-deps; }
