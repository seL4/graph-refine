(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

