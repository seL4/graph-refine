# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

from target_objects import target_dir, structs, functions
from target_objects import symbols, sections, rodata, pairings
import target_objects

import syntax
import pseudo_compile
import objdump
import logic
import re

syntax.set_arch('rv64')
f = open ('%s/kernel.elf.symtab' % target_dir)
objdump.install_syms (f)
f.close ()

f = open ('%s/CFunctions.txt' % target_dir)
syntax.parse_and_install_all (f, 'C')
f.close ()

#f = open ('%s/ASMFunctions_stack.txt' % target_dir)
f = open('%s/ASMFunctions.txt' % target_dir)
(astructs, afunctions, aconst_globals) = syntax.parse_and_install_all(f, 'ASM', skip_functions=['fastpath_call', 'fastpath_reply_recv', 'c_handle_syscall', 'init_freemem'])
f.close ()
assert not astructs
assert not aconst_globals

#assert logic.aligned_address_sanity (afunctions, symbols, 4)

f = open ('%s/kernel.elf.rodata' % target_dir)
objdump.install_rodata (f,
        [
            # These are the relevant sections for RISC-V.
            # However, due to the slow-down caused by rodata,
            # we probably want to target exactly the structures
            # we need. See below for those.
            #('Section', '.rodata'),
            #('Section', '.srodata'),

            # These are all the specific read-only symbols on RISC-V.
            # Uncomment as needed.
            ('Symbol', 'fault_messages'),
            ('Symbol', 'frameRegisters'),
            ('Symbol', 'gpRegisters'),
            ('Symbol', 'msgRegisters'),

            # Also present on RISC-V, but I'm fairly certain they're not needed.
            #('Symbol', 'ksDomSchedule'),
            #('Symbol', 'ksDomScheduleLength'),

            # These are the symbols from ARM, that seem to be
            # optimised away on RISC-V.
            #('Symbol', 'kernel_devices'),
	    #('Symbol', 'avail_p_regs'),
            #('Symbol', 'dev_p_regs')
        ]
)
f.close ()


print 'Pseudo-Compiling.'
pseudo_compile.compile_funcs (functions)

print 'Doing stack/inst logic.'

def make_pairings ():
    pairs = [(s, c_prefix + s)
             for s in functions
             for c_prefix in ['Kernel_C.', "Kernel_C.StrictC'"]
             if (c_prefix + s) in functions]
    target_objects.use_hooks.add ('stack_logic')
    import stack_logic
    stack_bounds = '%s/StackBounds.txt' % target_dir
    new_pairings = stack_logic.mk_stack_pairings (pairs, stack_bounds)
    pairings.update (new_pairings)

make_pairings ()

import inst_logic
inst_logic.add_inst_specs ()

print 'Checking.'
syntax.check_funs (functions)
