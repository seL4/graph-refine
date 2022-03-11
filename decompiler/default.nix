# Copyright (c) 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

# Packages the decompiler as a Nix derivation,
# and also produces a Docker image.

{
  pkgs ? import <nixpkgs> {},
  decompiler_dir ? ./.,
  polyml_src ? decompiler_dir + "/src/polyml",
  hol4_src ? decompiler_dir + "/src/HOL4",
  image_name ? "decompiler",
}:

with pkgs;
with lib;
with stdenv;

with (import ../nix/util.nix { inherit pkgs; });

let

  polyml = pkgs.polyml.overrideAttrs (_: {
    name = "polyml";
    src = cleanSourceWith {
      name = "polyml-source";
      src = polyml_src;
      filter = gitignoreFilter polyml_src;
    };
  });

  hol4-graph-decompiler = mkDerivation {
    name = "hol4-graph-decompiler";

    src = cleanSourceWith {
      name = "hol4-source";
      src = hol4_src;
      filter = gitignoreFilter hol4_src;
    };

    buildInputs = [ fontconfig graphviz polyml ];

    buildCommand = ''
      set -eu

      mkdir fonts
      cat ${fontconfig.out}/etc/fonts/fonts.conf > fonts/fonts.conf
      export FONTCONFIG_FILE=$PWD/fonts/fonts.conf

      cp -r "$src" "$out"
      chmod -R +w "$out"
      cd "$out"

      poly < tools/smart-configure.sml

      [ -x bin/build ]
      bin/build

      PATH="$out/bin:$PATH"
      cd examples/machine-code/graph
      Holmake
    '';
  };

  decompile-py = runCommand "decompile-py" {} ''
    mkdir -p "$out"
    cp --preserve=all "${decompiler_dir + "/decompile.py"}" "$out/decompile.py"
    (cd $out && ${python3.interpreter} -m compileall "decompile.py")
  '';

  decompiler = runCommand "decompiler" {} ''
    mkdir -p "$out/bin"
    cat > "$out/bin/decompile" <<EOF
    #!${runtimeShell}
    export HOL4_DIR="${hol4-graph-decompiler}"
    exec "${python3.interpreter}" "${decompile-py}/decompile.py" "\$@"
    EOF
    chmod +x "$out/bin/decompile"
  '';

  decompiler-image = dockerTools.streamLayeredImage {
    name = image_name;
    contents = [ bashInteractive coreutils polyml python3 ];
    config = { Entrypoint = "${decompiler}/bin/decompile"; };
  };

in { inherit decompiler decompiler-image; }
