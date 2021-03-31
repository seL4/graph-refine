#!/usr/bin/env python3

import sys


def rewrite_call_ret_addr_input(asm_lines):
    """
    Rewrite the last input parameter to a Call from r0 to r10.
    We identify the last parameter as the one following the `clock` parameter.
    """
    for line in range(len(asm_lines)):
        fields = asm_lines[line].split(' ')
        if len(fields) < 5 or fields[1] != 'Call':
            continue
        for field in range(4, len(fields)):
            if fields[field] == 'r0' and fields[field - 4] == 'clock':
                fields[field] = 'r10'
                asm_lines[line] = ' '.join(fields)
                break


def main(arg0, argv):
    if len(argv) != 1:
        print("Usage: %s ASMFunctions.txt" % arg0)
        return

    asm_fn = argv[0]
    with open(asm_fn) as asm_fh:
        asm_lines = asm_fh.readlines()

    rewrite_call_ret_addr_input(asm_lines)

    for line in asm_lines:
        sys.stdout.write(line)


if __name__ == '__main__':
    main(sys.argv[0], sys.argv[1:])
