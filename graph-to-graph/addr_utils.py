# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)
def phyAddrP(p_n,p):
    _,x = p.node_tags[p_n]
    f_name,g_addr = x
    return g_addr

def callNodes(p, fs= None):
    ret = [n for n in p.nodes if isCall(p.nodes[n])]
    if fs:
        ret = [n for n in ret if p.nodes[n].fname in fs]
    return ret

def gToPAddrP(n,p,may_multi=False,may_empty=False):
    matches = [x for x in p.node_tags if p.node_tags[x][1][1] == n and p.node_tags[1][0] != 'LoopReturn']
    if may_empty and not matches:
          return matches
    assert matches
    if may_multi:
        return matches
    assert len(matches) == 1
    return matches[0]

def isCall(node):
    return node.kind == 'Call'

def toHexs(l):
    return [hex(x) for x in l]
