# Copyright (c) 2022, Kry10 Limited.
# SPDX-License-Identifier: BSD-2-Clause

# Packages the decompiler with some extra tools and scripts, to make Docker
# images for producing graph-refine inputs other than CFunctions.txt.
# These can be useful when some other process (e.g. GitHub CI) is used to
# generate CFunctions.txt.
# - sel4-decompile can be used to perform decompilation and stack analysis,
#   assuming the kernel has already been compiled.
# - sel4-compile-decompile can additionally perform kernel compilation.

# We assume that PolyML and HOL4 sources have been checked out.
# These can be checked out using:
#   ../decompiler/setup-decompiler checkout --upstream
# These are used to pre-build a decompiler.

# For export-kernel-builds, we also assume l4v and isabelle checkouts.
# These are used to pre-build a standalone C parser.

{
  l4v_src ? ../../l4v,
  isabelle_src ? ../../isabelle,
  polyml_src ? ../decompiler/src/polyml,
  hol4_src ? ../decompiler/src/HOL4,
}:

let

  pins = import ../nix/pins.nix;
  inherit (pins) pkgs lib stdenv rosetta-pkgs;
  inherit (pins.herculesGitignore) gitignoreFilter;

  inherit (import ../nix/util.nix) explicit_sources_filter explicit_sources conj2 mk-check-env;
  inherit (import ../nix/sel4-deps.nix) sel4-deps;

  inherit (import ../decompiler { inherit polyml_src hol4_src; }) decompile-bin;

  isabelle-table-ml = explicit_sources "isabelle-table-ml" isabelle_src [
    "src/Pure/General/table.ML"
  ];

  graph-refine-seL4 = explicit_sources "graph-refine-seL4" ./. [
    "functions-tool.py"
    "target-ARM.py"
    "target-RISCV64.py"
  ];

  # The standalone C parser is needed to produce kernel.sigs.
  mk-arch-c-parser = arch: stdenv.mkDerivation {
    name = "c-parser-${arch}";
    src = lib.cleanSourceWith {
      name = "c-parser-src";
      src = l4v_src;
      filter = conj2 [ (gitignoreFilter l4v_src)
                       (explicit_sources_filter l4v_src [ "tools/c-parser" ]) ];
    };
    nativeBuildInputs = [ rosetta-pkgs.mlton pkgs.perl ];
    buildPhase = ''
      ISABELLE_HOME=${isabelle-table-ml} \
      SML_COMPILER=mlton \
      GLOBAL_MAKES_INCLUDED=true \
      make -C tools/c-parser/standalone-parser \
        "$PWD/tools/c-parser/standalone-parser/${arch}/c-parser"
    '';
    installPhase = ''
      mkdir -p "$out/bin"
      cp -a "tools/c-parser/standalone-parser/${arch}/c-parser" "$out/bin"
    '';
  };

  perl = "${pkgs.perl}/bin/perl";

  sel4-decompile-python =
    let python = pkgs.python3.withPackages (p: with p; [networkx]);
    in "${python}/bin/python";

  sel4-decompile-arch-cmd = arch:
    let
      ignore = builtins.readFile (pkgs.runCommand "sel4-decompile-${arch}" {} ''
        ${perl} -ne 'print $1 if /^IGNORE_${arch}\s*[\?:]?=\s*(\S*)\s*$/' ${./Makefile} > $out
      '');
      decompile = if ignore == ""
        then ''"${decompile-bin}/bin/decompile"''
        else ''"${decompile-bin}/bin/decompile" --ignore "${ignore}"'';
    in decompile;

  mk-arches = arches: rec {
    deriv_args = text: {
      inherit text;
      passthru = { inherit arches; };
      passAsFile = [ "text" ];
    };

    writeScriptBin = name: text: pkgs.runCommand name (deriv_args text) ''
      mkdir -p "$out/bin"
      mv "$textPath" "$out/bin/${name}"
      chmod +x "$out/bin/${name}"
    '';

    writeScript = name: text: pkgs.runCommand name (deriv_args text) ''
      mv "$textPath" "$out"
      chmod +x "$out"
    '';

    c-parser =
      let
        arch-case = arch: ''${arch}) exec ${mk-arch-c-parser arch}/bin/c-parser "$@";;'';
        script = writeScriptBin "c-parser" ''
          #!${pkgs.runtimeShell}
          set -euo pipefail
          case "$L4V_ARCH" in
            ${lib.concatStringsSep "\n  " (map arch-case arches)}
            *) echo "error: unknown L4V_ARCH: $L4V_ARCH" >&2; exit 1;;
          esac
        '';
      in script;

    # A wrapper that runs a given command in an environment that has
    # everything needed for building seL4 using the l4v kernel make files,
    # including a pre-built standalone C parser.
    sel4-build-env =
      let
        deriv_args = { nativeBuildInputs = [ pkgs.makeBinaryWrapper ]; };
        script = writeScript "sel4-build-env-exec" ''
          #!${pkgs.runtimeShell}
          exec "$@"
        '';
        wrapper = pkgs.runCommand "sel4-build-env" deriv_args ''
          makeWrapper "${script}" "$out" \
            --set PATH "${lib.makeBinPath sel4-deps}" \
            --set STANDALONE_C_PARSER_EXE "${c-parser}/bin/c-parser"
        '';
      in wrapper;

    sel4-decompile-script = let writeScriptDefault = writeScript; in
      { name ? "sel4-decompile", writeScript ? writeScriptDefault, decompile ? true }:
      let
        arch-case = arch: if decompile
          then ''${arch}) ${sel4-decompile-arch-cmd arch} "$TARGET_DIR/kernel";;''
          else ''${arch}) ;;'';

        script = ''
          #!${pkgs.runtimeShell}
          set -euo pipefail

          if [ $# -eq 0 ]; then
            echo "${name}: error: no arguments" >&2
            echo "${name} usage: ${name} TARGET_DIR..." >&2
            exit 1
          fi

          for TARGET_DIR in "$@"; do
            if [ ! -f "$TARGET_DIR/config.env" ]; then
              echo "${name}: error: $TARGET_DIR/config.env does not exist" >&2
              exit 1
            fi
          done

          for TARGET_DIR in "$@"; do
            export L4V_ARCH=$("${perl}" -ne 'print $1 if /^L4V_ARCH=(\S+)$/' "$TARGET_DIR/config.env")

            case "$L4V_ARCH" in
              ${lib.concatStringsSep "\n    " (map arch-case arches)}
              *) echo "${name}: error: unknown L4V_ARCH in $TARGET_DIR/config.env: $L4V_ARCH" >&2; exit 1;;
            esac

            if [ -f "$TARGET_DIR/CFunctions.txt" ]; then
              FUNCTIONS_ARG="--functions-list-out functions-list.txt"
            else
              FUNCTIONS_ARG=""
            fi

            "${sel4-decompile-python}" "${graph-refine-seL4}/functions-tool.py" \
              --target-dir "$TARGET_DIR" \
              --asm-functions-out ASMFunctions.txt \
              --stack-bounds-out StackBounds.txt \
              $FUNCTIONS_ARG

            cp "${graph-refine-seL4}/target-$L4V_ARCH.py" "$TARGET_DIR/target.py"
          done
        '';
      in writeScript name script;

    # For interactive use.
    sel4-decompile = sel4-decompile-script {};

    # For the Docker image.
    sel4-decompile-bin = sel4-decompile-script { writeScript = writeScriptBin; };

    # For development, skips the actual decompile, and just does the stuff after it.
    sel4-decompile-post = sel4-decompile-script { name = "sel4-decompile-post"; decompile = false; };

    sel4-decompiler-image = pkgs.dockerTools.streamLayeredImage {
      name = "sel4-decompiler";
      contents = with pkgs; [ bashInteractive coreutils sel4-decompile-bin ];
      config = { EntryPoint = [ "${sel4-decompile-bin}/bin/sel4-decompile" ]; };
    };
  };

in {

  inherit (mk-arches [ "ARM" "RISCV64" ])
    c-parser
    sel4-build-env
    sel4-decompile
    sel4-decompile-bin
    sel4-decompile-post
    sel4-decompiler-image;

}
