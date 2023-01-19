# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Dependencies for building seL4.

let

  inherit (import ./pins.nix) pkgs;
  inherit (import ./sel4-python.nix) sel4-python;
  inherit (import ./cross-tools.nix) cross-tools;

  deps = with pkgs; [
    bash
    cmake
    coreutils
    dtc
    findutils
    gnugrep
    gnumake
    ninja
    libxml2
    sel4-python
    which
  ];

  sel4-deps = deps ++ cross-tools;

in { inherit sel4-deps sel4-python cross-tools; }
