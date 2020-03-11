(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Loop

imports CTranslation
  "../../l4v/tools/asmrefine/SimplExport"

begin

install_C_file "loop.c"

ML {*
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "loop.c" |> the
  in fn () => the_csenv end
*}

setup {*
  DefineGlobalsList.define_globals_list_i "loop.c" @{typ globals}
*}

context loop_global_addresses begin

ML {*
val outfile = (openOut_relative @{theory} "CFunDump.txt");
  emit_C_everything @{context} (csenv ()) outfile;
  TextIO.closeOut outfile;
*}

end

end

