# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

'''
temporary work around for under-specified functions
'''

import re
import sys

if len(sys.argv) != 3:
    print "usage: %s original_file output_name" % sys.argv[0]
    sys.exit(-1)
original_name = sys.argv[1]
output_name = sys.argv[2]
original = open(original_name)

output = open(output_name, 'w')
while True:
    line = original.readline()
    if not line:
        break
    if 'instruction' in line:
        #print line
        x = line.split()
        if x[0] == "Function":
            next_line = original.readline()
            #drop these two lines
        else:
            output.write("%s Cond %s Err Op UnspecifiedPrecond Bool 0\n" % (x[0], x[2]))
    else:
        output.write(line)
output.close()
original.close()
