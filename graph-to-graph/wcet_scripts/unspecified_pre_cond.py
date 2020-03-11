#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

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
