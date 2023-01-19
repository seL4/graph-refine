# Copyright 2023 Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

# Cross-compilers used to generate kernel binaries.

let

  inherit (import ./pins.nix)
    mk-default-pkgs
    mk-arm-cross-pkgs;

in rec {

  mk-cross-pkgs = mk-pkgs: crossSystem:
    let cross-pkgs = mk-pkgs { inherit crossSystem; };
    in cross-pkgs.pkgsBuildTarget;

  mk-cross-tools = mk-pkgs: crossSystem:
    with (mk-cross-pkgs mk-pkgs crossSystem); [ gcc-unwrapped binutils-unwrapped ];

  x86-cross-tools =
    mk-cross-tools mk-default-pkgs { config = "x86_64-unknown-linux-gnu"; };

  riscv64-cross-tools =
    mk-cross-tools mk-default-pkgs { config = "riscv64-unknown-linux-gnu"; };

  arm-embedded-tools =
    mk-cross-tools mk-arm-cross-pkgs { config = "arm-none-eabi"; libc = "newlib"; };

  cross-tools = x86-cross-tools ++ riscv64-cross-tools ++ arm-embedded-tools;

}
