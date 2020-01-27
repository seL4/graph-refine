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
setup \<open>DefineGlobalsList.define_globals_list_i
  "input.c" @{typ globals}\<close>
locale target
  = input_global_addresses
begin
ML \<open>
emit_C_everything_relative @{context}
  (CalculateState.get_csenv @{theory} "input.c" |> the)
  "result.txt"
\<close>
end
end