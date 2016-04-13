import sys
import subprocess

if len(sys.argv) != 2:
   print 'expecting an imm file as argument'
   sys.exit(-1)

f_name = sys.argv[1]
target = 'new-gcc-O1'

imm = '/home/felixk/thesis/quoll/out/%s.imm' % f_name
imm_f = open(imm, 'r')
d = '/home/felixk/thesis/graph-to-graph/%s/dd_%s.imm' % (target,f_name)
di = '/home/felixk/thesis/graph-to-graph/%s/d_%s.imm' % (target,f_name)
d_f = open(d,'w')

for line in imm_f:
  lead = line[0]
  if lead in ['i','e']:
    d_f.write(line)

d_f.flush()

print 'diffing...'

diff_f = open ('./difff','w')

#finally, invoke diff, note quoll is on the left
#p = subprocess.Popen(["diff",d,di],stdout=subprocess.PIPE)
p = subprocess.Popen(["diff",d,di],stdout=diff_f)
ret = p.wait()
#out,err = p.communicate()

#write out to a file
#di = './difff'
#di_f = open(di,'w')
#di_f.write(out)
#di_f.flush()

