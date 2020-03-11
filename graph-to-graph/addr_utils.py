#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

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
