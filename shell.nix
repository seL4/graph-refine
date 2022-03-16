# Copyright 2020, Arm Limited
# Copyright 2022, Kry10 Limited
#
# SPDX-License-Identifier: MIT

{
  nixpkgs ? <nixpkgs>,
  pkgs ? import nixpkgs {},
  solver_config ? {},
}:

with pkgs;
with lib;
with (import nix/graph-refine.nix { inherit pkgs solver_config; });

let

  # Adapted from https://gitlab.com/arm-research/security/icecap/icecap
  python-with-my-packages = python310.withPackages (python-pkgs: with python-pkgs;
    let
      autopep8_1_4_3 = buildPythonPackage rec {
        pname = "autopep8";
        version = "1.4.3";
        src = fetchPypi {
          inherit pname version;
          sha256 = "13140hs3kh5k13yrp1hjlyz2xad3xs1fjkw1811gn6kybcrbblik";
        };
        propagatedBuildInputs = [
          pycodestyle
        ];
        doCheck = false;
        checkInputs = [ glibcLocales ];
        LC_ALL = "en_US.UTF-8";
      };

      cmake-format = buildPythonPackage rec {
        pname = "cmake_format";
        version = "0.4.5";
        src = fetchPypi {
          inherit pname version;
          sha256 = "0nl78yb6zdxawidp62w9wcvwkfid9kg86n52ryg9ikblqw428q0n";
        };
        propagatedBuildInputs = [
          jinja2
          pyyaml
        ];
        doCheck = false;
      };

      guardonce = buildPythonPackage rec {
        pname = "guardonce";
        version = "2.4.0";
        src = fetchPypi {
          inherit pname version;
          sha256 = "0sr7c1f9mh2vp6pkw3bgpd7crldmaksjfafy8wp5vphxk98ix2f7";
        };
        buildInputs = [
          nose
        ];
      };

      pyfdt = buildPythonPackage rec {
        pname = "pyfdt";
        version = "0.3";
        src = fetchPypi {
          inherit pname version;
          sha256 = "1w7lp421pssfgv901103521qigwb12i6sk68lqjllfgz0lh1qq31";
        };
      };

      sel4-deps = buildPythonPackage rec {
        pname = "sel4-deps";
        version = "0.3.1";
        src = fetchPypi {
          inherit pname version;
          sha256 = "09xjv4gc9cwanxdhpqg2sy2pfzn2rnrnxgjdw93nqxyrbpdagd5r";
        };
        postPatch = ''
          substituteInPlace setup.py --replace bs4 beautifulsoup4
        '';
        propagatedBuildInputs = [
          autopep8_1_4_3
          beautifulsoup4
          cmake-format
          future
          guardonce
          jinja2
          jsonschema
          libarchive-c
          lxml
          pexpect
          ply
          psutil
          pyaml
          pyelftools
          pyfdt
          setuptools
          six
          sh
        ];
      };

    in [ sel4-deps mypy networkx ]);

  mk_cross_pkgs = config:
    let pkgs_base = import nixpkgs { crossSystem = { inherit config; }; };
    in pkgs_base.pkgsBuildTarget;

  cross_configs = {
    riscv64 = "riscv64-unknown-linux-gnu";
    arm = "arm-none-eabi";
  };

  cross_pkgs = lib.mapAttrs (_: mk_cross_pkgs) cross_configs;
  cross_tools = lib.concatMap (p: [p.gcc-unwrapped p.binutils-unwrapped]) (lib.attrValues cross_pkgs);

  misc_tools = [
    cmakeCurses
    cpio
    dtc
    graph-refine-python
    libxml2
    mlton
    moreutils
    ninja
    python-with-my-packages
    solverlist
    strip-nondeterminism
  ];

in mkShell {
  packages = cross_tools ++ misc_tools ++ attrValues solvers;
  GRAPH_REFINE_SOLVERLIST_DIR = solverlist;
}
