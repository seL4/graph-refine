# Copyright (c) 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

# Packages the decompiler as a Nix derivation,
# and also produces a Docker image.

# This assumes that PolyML and HOL4 sources have been checked out.
# These can be checked out using:
#   ./setup-decompiler checkout --upstream

{
  polyml_src ? ./src/polyml,
  hol4_src ? ./src/HOL4,
}:

let

  pins = import ../nix/pins.nix;
  inherit (pins) pkgs lib stdenv;
  inherit (pins.herculesGitignore) gitignoreFilter;

  polyml = pkgs.polyml.overrideAttrs (_: {
    name = "polyml";
    src = lib.cleanSourceWith {
      name = "polyml-source";
      src = polyml_src;
      filter = gitignoreFilter polyml_src;
    };
  });

  hol4-graph-decompiler = stdenv.mkDerivation {
    name = "hol4-graph-decompiler";

    src = lib.cleanSourceWith {
      name = "hol4-source";
      src = hol4_src;
      filter = gitignoreFilter hol4_src;
    };

    buildInputs = [ pkgs.fontconfig pkgs.graphviz polyml ];

    buildCommand = ''
      set -eu

      mkdir fonts
      cat ${pkgs.fontconfig.out}/etc/fonts/fonts.conf > fonts/fonts.conf
      export FONTCONFIG_FILE=$PWD/fonts/fonts.conf

      cp -r "$src" "$out"
      chmod -R +w "$out"
      cd "$out"

      poly < tools/smart-configure.sml
      bin/build

      PATH="$out/bin:$PATH"
      cd examples/machine-code/graph
      Holmake
    '';
  };

  decompile-py = pkgs.runCommand "decompile-py" {} ''
    mkdir -p "$out"
    cp --preserve=all "${./decompile.py}" "$out/decompile.py"
    (cd $out && ${pkgs.python3.interpreter} -m compileall "decompile.py")
  '';

  decompile_script = ''
    #!${pkgs.runtimeShell}
    export HOL4_DIR="${hol4-graph-decompiler}"
    exec "${pkgs.python3.interpreter}" "${decompile-py}/decompile.py" "$@"
  '';

  # For the Docker customisation layer, the script should be in a `bin` directory.
  decompile-bin = pkgs.writeScriptBin "decompile" decompile_script;

  # But for non-Docker use, a plain script is more convenient.
  decompile = pkgs.writeScript "decompile" decompile_script;

  decompiler-image = pkgs.dockerTools.streamLayeredImage {
    name = "decompiler";
    contents = with pkgs; [ bashInteractive coreutils polyml python3 decompile-bin ];
    config = { Entrypoint = [ "${decompile-bin}/bin/decompile" ]; };
  };

in { inherit decompile decompile-bin decompiler-image; }
