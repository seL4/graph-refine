# Copyright 2020 Arm Limited
# Copyright 2022 Kry10 Limited
#
# SPDX-License-Identifier: MIT

# A Python environment suitable for building seL4, adapted from:
# https://gitlab.com/icecap-project/icecap/-/blob/main/nix/framework/overlay/python-overrides.nix

let

  inherit (import ./pins.nix) pkgs;

  sel4-python = pkgs.python3.withPackages (python-pkgs: with python-pkgs;
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
          types-pyyaml
        ];
      };

    in [ sel4-deps mypy ]);

in { inherit sel4-python; }
