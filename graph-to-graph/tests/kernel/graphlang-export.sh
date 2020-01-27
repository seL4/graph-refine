#! /bin/bash

set -eux
script_name="$0"

show_help(){
    set +x

    message="${1:-}"
    if ! [ -z "$message" ]; then
        echo
        echo "$message"
        echo
    fi

    echo "Usage: $script_name <c_input_file> [output_file]"
    echo
    echo "Uses the L4V C parser and AsmRefine to extract the"
    echo "GraphLang representation of \$c_input_file."
    echo "Writes the result to CFunctions.txt, unless"
    echo "\$output_file is specified."

    exit 1
}

if [ $# -lt 1 -o $# -gt 2 ]; then
    show_help "Expected 1 or 2 arguments, got $#."
fi

c_file="$(realpath "$1")"
output_file="$(realpath "${2:-"CFunctions.txt"}")"

L4V_ARCH="${L4V_ARCH:?Must set L4V_ARCH}"
TV_ROOT="${TV_ROOT:?Must set TV_ROOT.

TV_ROOT should point to a sync'd and init'd verification checkout, i.e. it
should point to the parent directory of l4v, graph-refine, HOL4, etc.}"
TV_ROOT="$(realpath "${TV_ROOT}")"

THY="$(cat <<END
theory "tmp"
imports
    "CParser.CTranslation"
    "AsmRefine.GlobalsSwap"
    "AsmRefine.SimplExport"
begin
declare [[populate_globals=true]]
typedecl machine_state
typedecl cghost_state
install_C_file "input.c"
  [machinety=machine_state, ghostty=cghost_state]
setup \\<open>DefineGlobalsList.define_globals_list_i
  "input.c" @{typ globals}\\<close>
locale target
  = input_global_addresses
begin
ML \\<open>
emit_C_everything_relative @{context}
  (CalculateState.get_csenv @{theory} "input.c" |> the)
  "result.txt"
\<close>
end
end
END
)"
ROOT="$(cat <<END
session SimplExport = AsmRefine +
    theories "tmp"
END
)"

pushd $(mktemp -d)
pwd
cp "$c_file" input.c
echo -n "$THY" > tmp.thy
echo -n "$ROOT" > ROOT
"$TV_ROOT"/isabelle/bin/isabelle build -d "$TV_ROOT"/l4v -D . -f
cp result.txt "$output_file"
popd
