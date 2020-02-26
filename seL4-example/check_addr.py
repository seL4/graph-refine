import sys

asm_fn = ''
bin_fn = ''
out_fn = ''
bin_lines = []
asm_lines = []
out_lines = []
bin_branch_map = {}

branches = ('beq', 'bne',
            'blt', 'bge',
            'bltu', 'bgeu',
            'bltz', 'bgez',
            'beqz', 'bnez',
            'blez', 'bgtz',
            'j'
            )



def build_branch_map():
    global bin_branch_map
    for l in bin_lines:
        f = l.split()
        if len(f) < 3:
            continue
        addr = f[0].strip()
        addr = addr[:-1]
        op = f[2].strip()
        if op in branches:
            targets = f[3].split(',')
            for t in targets:
                if t.startswith('ffffffff'):
                    ta = t.strip()
                    addr = addr[8:]
                    ta = ta[8:]
                    bin_branch_map[addr] = ta
                    #print "line %s map %s to %s" % (l, addr, ta)

    #print bin_branch_map

def check_cond_map():
    global out_lines
    out_lines = []
    i = 0
    while i < len(asm_lines):
        l = asm_lines[i]
        print l
        f = l.split()
        if len(f) < 4:
            print 'append %s' %l
            out_lines.append(l)
            i = i + 1
            continue

        addr = f[0].strip()
        op = f[1].strip()
        lb = f[2].strip()
        rb = f[3].strip()

        # j instruction
        if op == 'Basic' and rb == '0' and (not lb == 'Ret') and len(addr) == 10:
            addr = addr[2:].lower()
            jaddr = lb.strip()[2:].lower()
            if not addr in bin_branch_map.keys():
                out_lines.append(l)
                i = i + 1
                continue

            ta = bin_branch_map[addr]
            if not ta == jaddr:
               print 'Invalid j at %s wrong %s right %s' % (addr, jaddr, ta)
               f[2] = '0x' + ta.upper()
               print 'new line %s ' % ' '.join(f)
            out_lines.append(' '.join(f) + '\n')
            i = i + 1
            continue


        if op == 'Cond' and ((lb == 'Err') or (rb == 'Err')):
            out_lines.append(l)
            i = i + 1
            continue

        if op == 'Cond':
            addr = f[0].strip()
            addr = addr[2:].lower()
            lc = asm_lines[i + 1]
            lcf = lc.split()

            #print lcf
            assert lcf[1].strip() == 'Basic'
            lcf_addr = lcf[2].strip()
            lcf_addr = lcf_addr[2:].lower()
            ta = bin_branch_map[addr]
            #print 'addr %s lcf %s ta %s', (addr, lcf_addr, ta)
            if not ta == lcf_addr:
                print 'Invalid branch at %s wrong %s right %s' % (addr, lcf_addr, ta)
                lcf[2] = '0x' + ta.upper()
                print 'new line %s' % ' '.join(lcf)

            out_lines.append(l)
            out_lines.append(' '.join(lcf) + '\n')
            rc = asm_lines[i + 2]
            out_lines.append(rc)
            i = i + 3
        else:
            print 'al %s' % l
            out_lines.append(l)
            i = i + 1

def main(argv):
    if len(argv) != 3:
        print "Usage: ASM_filename elf_dump_file output_file"
        return


    global asm_fn
    global bin_fn
    global out_fn
    global bin_lines
    global asm_lines
    global out_lines

    asm_fn = argv[0]
    bin_fn = argv[1]
    f = open(asm_fn)
    asm_lines = f.readlines()
    f.close()

    f = open(bin_fn)
    bin_lines = f.readlines()
    f.close()
    build_branch_map()
    check_cond_map()

    out_fn = argv[2]
    f = open(out_fn, 'w')
    for l in out_lines:
        f.write(l)
    f.close()
    pass

if __name__ == '__main__':
    main(sys.argv[1:])
