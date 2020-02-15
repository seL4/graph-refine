#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from syntax import (Expr, mk_var, Node, true_term, false_term,
                    fresh_name, word32T, word8T, mk_eq, mk_word32, builtinTs)
import syntax

from target_objects import functions, pairings, trace, printout
import sys
import logic
from logic import azip

class Abort(Exception):
    pass

last_problem = [None]

class Problem:
    def __init__ (self, pairing, name = None):
        if name == None:
            name = pairing.name
        print 'problem name %s pairing %s' % (name, pairing)
        self.name = 'Problem (%s)' % name
        self.pairing = pairing
        #print 'pairing:\n'
        #print pairing
        #print type(pairing)
        self.nodes = {}
        self.vs = {}
        self.next_node_name = 1
        self.preds = {}
        self.loop_data = {}
        self.node_tags = {}
        self.node_tag_revs = {}
        self.inline_scripts = {}
        self.entries = []
        self.outputs = {}
        self.tarjan_order = []
        self.loop_var_analysis_cache = {}

        self.known_eqs = {}
        self.cached_analysis = {}
        self.hook_tag_hints = {}

        last_problem[0] = self

    def fail_msg (self):
        return 'FAILED %s (size %05d)' % (self.name, len(self.nodes))

    def alloc_node (self, tag, detail, loop_id = None, hint = None):
        name = self.next_node_name
        self.next_node_name = name + 1

        self.node_tags[name] = (tag, detail)
        self.node_tag_revs.setdefault ((tag, detail), [])
        self.node_tag_revs[(tag, detail)].append (name)

        if loop_id != None:
            self.loop_data[name] = ('Mem', loop_id)

        return name

    def fresh_var (self, name, typ):
        name = fresh_name (name, self.vs, typ)
        return mk_var (name, typ)

    def clone_function (self, fun, tag):
        self.nodes = {}
        self.vs = syntax.get_vars (fun)
        for n in fun.reachable_nodes ():
            self.nodes[n] = fun.nodes[n]
            detail = (fun.name, n)
            self.node_tags[n] = (tag, detail)
            self.node_tag_revs.setdefault ((tag, detail), [])
            self.node_tag_revs[(tag, detail)].append (n)
        self.outputs[tag] = fun.outputs
        self.entries = [(fun.entry, tag, fun.name, fun.inputs)]
        self.next_node_name = max (self.nodes.keys () + [2]) + 1
        self.inline_scripts[tag] = []

    def add_function (self, fun, tag, node_renames, loop_id = None):
        if not fun.entry:
            printout ('Aborting %s: underspecified %s' % (
                self.name, fun.name))
            raise Abort ()
        node_renames.setdefault('Ret', 'Ret')
        node_renames.setdefault('Err', 'Err')
        new_node_renames = {}
        vs = syntax.get_vars (fun)
        vs = dict ([(v, fresh_name (v, self.vs, vs[v])) for v in vs])
        ns = fun.reachable_nodes ()
        check_no_symbols ([fun.nodes[n] for n in ns])
        for n in ns:
            assert n not in node_renames
            node_renames[n] = self.alloc_node (tag, (fun.name, n),
                                               loop_id = loop_id, hint = n)
            new_node_renames[n] = node_renames[n]
        for n in ns:
            self.nodes[node_renames[n]] = syntax.copy_rename (
                fun.nodes[n], (vs, node_renames))

        return (new_node_renames, vs)

    def add_entry_function (self, fun, tag):
        (ns, vs) = self.add_function (fun, tag, {})
        #print 'add func\n'
        #print fun
        #print tag
        entry = ns[fun.entry]
        args = [(vs[v], typ) for (v, typ) in fun.inputs]
        rets = [(vs[v], typ) for (v, typ) in fun.outputs]
        self.entries.append((entry, tag, fun.name, args))
        self.outputs[tag] = rets

        self.inline_scripts[tag] = []
        #print args
        #print rets
        #print entry
        #print 'done add func\n'
        return (args, rets, entry)

    def get_entry_details (self, tag):
        [(e, t, fname, args)] = [(e, t, fname, args)
                                 for (e, t, fname, args) in self.entries if t == tag]
        return (e, fname, args)

    def get_entry (self, tag):
        (e, fname, args) = self.get_entry_details (tag)
        return e

    def tags (self):
        return self.outputs.keys ()

    def entry_exit_renames (self, tags = None):
        """computes the rename set of a function's formal parameters
        to the actual input/output variable names at the various entry
        and exit points"""
        mk = lambda xs, ys: dict ([(x[0], y[0]) for (x, y) in
                                   azip (xs, ys)])
        renames = {}
        if tags == None:
            tags = self.tags ()
        for tag in tags:
            (_, fname, args) = self.get_entry_details (tag)
            fun = functions[fname]
            out = self.outputs[tag]
            renames[tag + '_IN'] = mk (fun.inputs, args)
            renames[tag + '_OUT'] = mk (fun.outputs, out)
        return renames

    def redirect_conts (self, reds):
        for node in self.nodes.itervalues():
            if node.kind == 'Cond':
                node.left = reds.get(node.left, node.left)
                node.right = reds.get(node.right, node.right)
            else:
                node.cont = reds.get(node.cont, node.cont)

    def do_analysis (self):
        self.cached_analysis.clear ()
        self.compute_preds ()
        self.do_loop_analysis ()

    def mk_node_graph (self, node_subset = None):
        if node_subset == None:
            node_subset = self.nodes
        '''
		print 'node begin \n'
		for n in self.nodes:
			print type(n)
			print '\t'
			print self.nodes
			print n
		print 'node end \n'

		for n in node_subset:
			print 'cont '
			print n
			print ' '
			print self.nodes[n].get_conts()
			print 'contdone\n'
		'''
        return dict ([(n, [c for c in self.nodes[n].get_conts ()
                           if c in node_subset])
                      for n in node_subset])

    def do_loop_analysis (self):
        entries = [e for (e, tag, nm, args) in self.entries]
        #print 'zzzu'
        #print self.name
        #print self.next_node_name
        '''	
		for (ee, tt, nn, aa) in self.entries:
			print ee
			print '\n'
			print tt
			print '\n'
			print nn
			print '\n'
			print aa
			print '\n'
		print 'zzzz\n'
		'''

        self.loop_data = {}

        graph = self.mk_node_graph ()
        comps = logic.tarjan (graph, entries)
        self.tarjan_order = []
        #print entries
        #print graph
        #print comps
        for (head, tail) in comps:
            self.tarjan_order.append (head)
            self.tarjan_order.extend (tail)
            if not tail and head not in graph[head]:
                #print 'loop cont (%d %s)' % (head, tail)
                continue
            #print 'loop (%d %s)' % (head, tail)
            trace ('Loop (%d, %s)' % (head, tail))

            loop_set = set (tail)
            loop_set.add (head)

            r = self.force_single_loop_return (head, loop_set)
            if r != None:
                tail.append (r)
                loop_set.add (r)
                self.tarjan_order.append (r)
                self.compute_preds ()

            self.loop_data[head] = ('Head', loop_set)
            #print 'set loop head'
            #print self.loop_data[head]
            #print head
            #print self.nodes[head]
            #print 'done'
            for t in tail:
                self.loop_data[t] = ('Mem', head)

        # put this in first-to-last order.
        self.tarjan_order.reverse ()

    def check_no_inner_loops (self):
        for loop in self.loop_heads ():
            check_no_inner_loop (self, loop)

    def force_single_loop_return (self, head, loop_set):
        rets = [n for n in self.preds[head] if n in loop_set]
        if (len (rets) == 1 and rets[0] != head and
                self.nodes[rets[0]].is_noop ()):
            return None
        r = self.alloc_node (self.node_tags[head][0],
                             'LoopReturn', loop_id = head)
        self.nodes[r] = Node ('Basic', head, [])
        for r2 in rets:
            self.nodes[r2] = syntax.copy_rename (self.nodes[r2],
                                                 ({}, {head: r}))
        return r

    def splittable_points (self, n):
        """splittable points are points which when removed, the loop
        'splits' and ceases to be a loop.

        equivalently, the set of splittable points is the intersection
        of all sub-loops of the loop."""
        head = self.loop_id (n)
        assert head != None
        k = ('Splittables', head)
        if k in self.cached_analysis:
            return self.cached_analysis[k]

        # check if the head point is a split (the inner loop
        # check does exactly that)
        if has_inner_loop (self, head):
            head = logic.get_one_loop_splittable (self,
                                                  self.loop_body (head))
            if head == None:
                return set ()

        splits = self.get_loop_splittables (head)
        self.cached_analysis[k] = splits
        return splits

    def get_loop_splittables (self, head):
        loop_set = self.loop_body (head)
        splittable = dict ([(n, False) for n in loop_set])
        arc = [head]
        n = head
        while True:
            ns = [n2 for n2 in self.nodes[n].get_conts ()
                  if n2 in loop_set]
            ns2 = [x for x in ns if x == head or x not in arc]
            #n = ns[0]
            n = ns2[0]
            arc.append (n)
            splittable[n] = True
            if n == head:
                break
        last_descs = {}
        for i in range (len (arc)):
            last_descs[arc[i]] = i
        def last_desc (n):
            if n in last_descs:
                return last_descs[n]
            n2s = [n2 for n2 in self.nodes[n].get_conts()
                   if n2 in loop_set]
            last_descs[n] = None
            for n2 in n2s:
                x = last_desc(n2)
                if last_descs[n] == None or x >= last_descs[n]:
                    last_descs[n] = x
            return last_descs[n]
        for i in range (len (arc)):
            max_arc = max ([last_desc (n)
                            for n in self.nodes[arc[i]].get_conts ()
                            if n in loop_set])
            for j in range (i + 1, max_arc):
                splittable[arc[j]] = False
        return set ([n for n in splittable if splittable[n]])

    def loop_heads (self):
        return [n for n in self.loop_data
                if self.loop_data[n][0] == 'Head']

    def loop_id (self, n):
        if n not in self.loop_data:
            return None
        elif self.loop_data[n][0] == 'Head':
            return n
        else:
            assert self.loop_data[n][0] == 'Mem'
            return self.loop_data[n][1]

    def loop_body (self, n):
        head = self.loop_id (n)
        return self.loop_data[head][1]

    def compute_preds (self):
        self.preds = logic.compute_preds (self.nodes)

    def var_dep_outputs (self, n):
        return self.outputs[self.node_tags[n][0]]

    def compute_var_dependencies (self):
        if 'var_dependencies' in self.cached_analysis:
            return self.cached_analysis['var_dependencies']
        var_deps = logic.compute_var_deps (self.nodes,
                                           self.var_dep_outputs, self.preds)
        var_deps2 = dict ([(n, dict ([(v, None)
                                      for v in var_deps.get (n, [])]))
                           for n in self.nodes])
        self.cached_analysis['var_dependencies'] = var_deps2
        return var_deps2

    def get_loop_var_analysis (self, var_deps, n):
        head = self.loop_id (n)
        assert head, n
        assert n in self.splittable_points (n)
        loop_sort = tuple (sorted (self.loop_body (head)))
        node_data = [(self.nodes[n2], sorted (self.preds[n]),
                      sorted (var_deps[n2].keys ()))
                     for n2 in loop_sort]
        k = (n, loop_sort)
        data = (node_data, n)
        if k in self.loop_var_analysis_cache:
            for (data2, va) in self.loop_var_analysis_cache[k]:
                if data2 == data:
                    return va
        va = logic.compute_loop_var_analysis (self, var_deps, n)
        group = self.loop_var_analysis_cache.setdefault (k, [])
        group.append ((data, va))
        del group[:-10]
        return va

    def save_graph (self, fname):
        cols = mk_graph_cols (self.node_tags)
        save_graph (self.nodes, fname, cols = cols,
                    node_tags = self.node_tags)

    def save_graph_summ (self, fname):
        node_ids = {}
        def is_triv (n):
            if n not in self.nodes:
                return False
            if len (self.preds[n]) != 1:
                return False
            node = self.nodes[n]
            if node.kind == 'Basic':
                return (True, node.cont)
            elif node.kind == 'Cond' and node.right == 'Err':
                return (True, node.left)
            else:
                return False
        for n in self.nodes:
            if n in node_ids:
                continue
            ns = []
            while is_triv (n):
                ns.append (n)
                n = is_triv (n)[1]
            for n2 in ns:
                node_ids[n2] = n
        nodes = {}
        for n in self.nodes:
            if is_triv (n):
                continue
            nodes[n] = syntax.copy_rename (self.nodes[n],
                                           ({}, node_ids))
        cols = mk_graph_cols (self.node_tags)
        save_graph (nodes, fname, cols = cols,
                    node_tags = self.node_tags)

    def serialise (self):
        ss = ['Problem']
        for (n, tag, fname, inputs) in self.entries:
            xs = ['Entry', '%d' % n, tag, fname,
                  '%d' % len (inputs)]
            for (nm, typ) in inputs:
                xs.append (nm)
                typ.serialise (xs)
            xs.append ('%d' % len (self.outputs[tag]))
            for (nm, typ) in self.outputs[tag]:
                xs.append (nm)
                typ.serialise (xs)
            ss.append (' '.join (xs))
        for n in self.nodes:
            xs = ['%d' % n]
            self.nodes[n].serialise (xs)
            ss.append (' '.join (xs))
        ss.append ('EndProblem')
        return ss

    def save_serialise (self, fname):
        ss = self.serialise ()
        f = open (fname, 'w')
        for s in ss:
            f.write (s + '\n')
        f.close ()

    def pad_merge_points (self):
        self.compute_preds ()

        arcs = [(pred, n) for n in self.preds
                if len (self.preds[n]) > 1
                if n in self.nodes
                for pred in self.preds[n]
                if (self.nodes[pred].kind != 'Basic'
                    or self.nodes[pred].upds != [])]

        for (pred, n) in arcs:
            (tag, _) = self.node_tags[pred]
            name = self.alloc_node (tag, 'MergePadding')
            self.nodes[name] = Node ('Basic', n, [])
            self.nodes[pred] = syntax.copy_rename (self.nodes[pred],
                                                   ({}, {n: name}))

    def function_call_addrs (self):
        return [(n, self.nodes[n].fname)
                for n in self.nodes if self.nodes[n].kind == 'Call']

    def function_calls (self):
        return set ([fn for (n, fn) in self.function_call_addrs ()])

    def get_extensions (self):
        if 'extensions' in self.cached_analysis:
            return self.cached_analysis['extensions']
        extensions = set ()
        for node in self.nodes.itervalues ():
            extensions.update (syntax.get_extensions (node))
        self.cached_analysis['extensions'] = extensions
        return extensions

    def replay_inline_script (self, tag, script):
        for (detail, idx, fname) in script:
            n = self.node_tag_revs[(tag, detail)][idx]
            assert self.nodes[n].kind == 'Call', self.nodes[n]
            assert self.nodes[n].fname == fname, self.nodes[n]
            inline_at_point (self, n, do_analysis = False)
        if script:
            self.do_analysis ()

    def is_reachable_from (self, source, target):
        '''discover if graph addr "target" is reachable
                from starting node "source"'''
        k = ('is_reachable_from', source)
        if k in self.cached_analysis:
            reachable = self.cached_analysis[k]
            if target in reachable:
                return reachable[target]

        reachable = {}
        visit = [source]
        while visit:
            n = visit.pop ()
            if n not in self.nodes:
                continue
            for n2 in self.nodes[n].get_conts ():
                if n2 not in reachable:
                    reachable[n2] = True
                    visit.append (n2)
        for n in list (self.nodes) + ['Ret', 'Err']:
            if n not in reachable:
                reachable[n] = False
        self.cached_analysis[k] = reachable
        return reachable[target]

    def is_reachable_without (self, cutpoint, target):
        '''discover if graph addr "target" is reachable
                without visiting node "cutpoint"
                (an oddity: cutpoint itself is considered reachable)'''
        k = ('is_reachable_without', cutpoint)
        if k in self.cached_analysis:
            reachable = self.cached_analysis[k]
            if target in reachable:
                return reachable[target]

        reachable = dict ([(self.get_entry (t), True)
                           for t in self.tags ()])
        for n in self.tarjan_order + ['Ret', 'Err']:
            if n in reachable:
                continue
            reachable[n] = bool ([pred for pred in self.preds[n]
                                  if pred != cutpoint
                                  if reachable.get (pred) == True])
        self.cached_analysis[k] = reachable
        return reachable[target]

def deserialise (name, lines):
    assert lines[0] == 'Problem', lines[0]
    assert lines[-1] == 'EndProblem', lines[-1]
    i = 1
    # not easy to reconstruct pairing
    p = Problem (pairing = None, name = name)
    while lines[i].startswith ('Entry'):
        bits = lines[i].split ()
        en = int (bits[1])
        tag = bits[2]
        fname = bits[3]
        (n, inputs) = syntax.parse_list (syntax.parse_lval, bits, 4)
        (n, outputs) = syntax.parse_list (syntax.parse_lval, bits, n)
        assert n == len (bits), (n, bits)
        p.entries.append ((en, tag, fname, inputs))
        p.outputs[tag] = outputs
        i += 1
    for i in range (i, len (lines) - 1):
        bits = lines[i].split ()
        n = int (bits[0])
        node = syntax.parse_node (bits, 1)
        p.nodes[n] = node
    return p

# trivia

def check_no_symbols (nodes):
    import pseudo_compile
    symbs = pseudo_compile.nodes_symbols (nodes)
    if not symbs:
        return
    printout ('Aborting %s: undefined symbols %s' % (self.name, symbs))
    raise Abort ()

# printing of problem graphs

def sanitise_str (s):
    return s.replace ('"', '_').replace ("'", "_").replace (' ', '')

def graph_name (nodes, node_tags, n, prev=None):
    if type (n) == str:
        return 't_%s_%d' % (n, prev)
    if n not in nodes:
        return 'unknown_%d' % n
    if n not in node_tags:
        ident = '%d' % n
    else:
        (tag, details) = node_tags[n]
        if len (details) > 1 and logic.is_int (details[1]):
            ident = '%d_%s_%s_0x%x' % (n, tag,
                                       details[0], details[1])
        elif type (details) != str:
            details = '_'.join (map (str, details))
            ident = '%d_%s_%s' % (n, tag, details)
        else:
            ident = '%d_%s_%s' % (n, tag, details)
    ident = sanitise_str (ident)
    node = nodes[n]
    if node.kind == 'Call':
        return 'fcall_%s' % ident
    if node.kind == 'Cond':
        return ident
    if node.kind == 'Basic':
        return 'ass_%s' % ident
    assert not 'node kind understood'

def graph_node_tooltip (nodes, n):
    if n == 'Err':
        return 'Error point'
    if n == 'Ret':
        return 'Return point'
    node = nodes[n]
    if node.kind == 'Call':
        return "%s: call to '%s'" % (n, sanitise_str (node.fname))
    if node.kind == 'Cond':
        return '%s: conditional node' % n
    if node.kind == 'Basic':
        var_names = [sanitise_str (x[0][0]) for x in node.upds]
        return '%s: assignment to [%s]' % (n, ', '.join (var_names))
    assert not 'node kind understood'

def graph_edges (nodes, n):
    node = nodes[n]
    if node.is_noop ():
        return [(node.get_conts () [0], 'N')]
    elif node.kind == 'Cond':
        return [(node.left, 'T'), (node.right, 'F')]
    else:
        return [(node.cont, 'C')]

def get_graph_font (n, col):
    font = 'fontname = "Arial", fontsize = 20, penwidth=3'
    if col:
        font = font + ', color=%s, fontcolor=%s' % (col, col)
    return font

def get_graph_loops (nodes):
    graph = dict ([(n, [c for c in nodes[n].get_conts ()
                        if type (c) != str]) for n in nodes])
    graph['ENTRY'] = list (nodes)
    comps = logic.tarjan (graph, ['ENTRY'])
    comp_ids = {}
    for (head, tail) in comps:
        comp_ids[head] = head
        for n in tail:
            comp_ids[n] = head
    loops = set ([(n, n2) for n in graph for n2 in graph[n]
                  if comp_ids[n] == comp_ids[n2]])
    return loops

def make_graph (nodes, cols, node_tags = {}, entries = []):
    graph = []
    graph.append ('digraph foo {')

    loops = get_graph_loops (nodes)

    for n in nodes:
        n_nm = graph_name (nodes, node_tags, n)
        f = get_graph_font (n, cols.get (n))
        graph.append ('%s [%s\n label="%s"\n tooltip="%s"];' % (n,
                                                                f, n_nm, graph_node_tooltip (nodes, n)))
        for (c, l) in graph_edges (nodes, n):
            if c in ['Ret', 'Err']:
                c_nm = '%s_%s' % (c, n)
                if c == 'Ret':
                    f2 = f + ', shape=doubleoctagon'
                else:
                    f2 = f + ', shape=Mdiamond'
                graph.append ('%s [label="%s", %s];'
                              % (c_nm, c, f2))
            else:
                c_nm = c
            ft = f
            if (n, c) in loops:
                ft = f + ', penwidth=6'
            graph.append ('%s -> %s [label=%s, %s];' % (
                n, c_nm, l, ft))

    for (i, (n, tag, inps)) in enumerate (entries):
        f = get_graph_font (n, cols.get (n))
        nm1 = tag + ' ENTRY_POINT'
        nm2 = 'entry_point_%d' % i
        graph.extend (['%s -> %s [%s];' % (nm2, n, f),
                       '%s [label = "%s", shape=none, %s];' % (nm2, nm1, f)])

    graph.append ('}')
    return graph

def print_graph (nodes, cols = {}, entries = []):
    for line in make_graph (nodes, cols, entries):
        print line

def save_graph (nodes, fname, cols = {}, entries = [], node_tags = {}):
    f = open (fname, 'w')
    for line in make_graph (nodes, cols = cols, node_tags = node_tags,
                            entries = entries):
        f.write (line + '\n')
    f.close ()

def mk_graph_cols (node_tags):
    known_cols = {'C': "forestgreen", 'ASM_adj': "darkblue",
                  'ASM': "darkorange"}
    cols = {}
    for n in node_tags:
        if node_tags[n][0] in known_cols:
            cols[n] = known_cols[node_tags[n][0]]
    return cols

def make_graph_with_eqs (p, invis = False):
    if invis:
        invis_s = ', style=invis'
    else:
        invis_s = ''
    cols = mk_graph_cols (p.node_tags)
    graph = make_graph (p.nodes, cols = cols)
    graph.pop ()
    for k in p.known_eqs:
        if k == 'Hyps':
            continue
        (n_vc_x, tag_x) = k
        nm1 = graph_name (p.nodes, p.node_tags, n_vc_x[0])
        for (x, n_vc_y, tag_y, y, hyps) in p.known_eqs[k]:
            nm2 = graph_name (p.nodes, p.node_tags, n_vc_y[0])
            graph.extend ([('%s -> %s [ dir = back, color = blue, '
                            'penwidth = 3, weight = 0 %s ]')
                           % (nm2, nm1, invis_s)])
    graph.append ('}')
    return graph

def save_graph_with_eqs (p, fname = 'diagram.dot', invis = False):
    graph = make_graph_with_eqs (p, invis = invis)
    f = open (fname, 'w')
    for s in graph:
        f.write (s + '\n')
    f.close ()

def get_problem_vars (p):
    inout = set.union (* ([set(xs) for xs in p.outputs.itervalues ()]
                          + [set (args) for (_, _, _, args) in p.entries]))

    vs = dict(inout)
    for node in p.nodes.itervalues():
        syntax.get_node_vars(node, vs)
    return vs

def is_trivial_fun (fun):
    for node in fun.nodes.itervalues ():
        if node.is_noop ():
            continue
        if node.kind == 'Call':
            return False
        elif node.kind == 'Basic':
            for (lv, v) in node.upds:
                if v.kind not in ['Var', 'Num']:
                    return False
        elif node.kind == 'Cond':
            if node.cond.kind != 'Var' and node.cond not in [
                    true_term, false_term]:
                return False
    return True

last_alt_nodes = [0]

def avail_val (vs, typ):
    for (nm, typ2) in vs:
        if typ2 == typ:
            return mk_var (nm, typ2)
    return logic.default_val (typ)

def inline_at_point (p, n, do_analysis = True):
    node = p.nodes[n]
    if node.kind != 'Call':
        return

    f_nm = node.fname
    fun = functions[f_nm]
    (tag, detail) = p.node_tags[n]
    idx = p.node_tag_revs[(tag, detail)].index (n)
    p.inline_scripts[tag].append ((detail, idx, f_nm))

    trace ('Inlining %s into %s' % (f_nm, p.name))
    if n in p.loop_data:
        trace ('  inlining into loop %d!' % p.loop_id (n))

    ex = p.alloc_node (tag, (f_nm, 'RetToCaller'))

    (ns, vs) = p.add_function (fun, tag, {'Ret': ex})
    en = ns[fun.entry]

    inp_lvs = [(vs[v], typ) for (v, typ) in fun.inputs]
    p.nodes[n] = Node ('Basic', en, azip (inp_lvs, node.args))

    out_vs = [mk_var (vs[v], typ) for (v, typ) in fun.outputs]
    p.nodes[ex] = Node ('Basic', node.cont, azip (node.rets, out_vs))

    p.cached_analysis.clear ()

    if do_analysis:
        p.do_analysis ()

    trace ('Problem size now %d' % len(p.nodes))
    sys.stdin.flush ()

    return ns.values ()

def loop_body_inner_loops (p, head, loop_body):
    loop_set_all = set (loop_body)
    loop_set = loop_set_all - set ([head])
    graph = dict([(n, [c for c in p.nodes[n].get_conts ()
                       if c in loop_set])
                  for n in loop_set_all])

    comps = logic.tarjan (graph, [head])
    assert sum ([1 + len (t) for (_, t) in comps]) == len (loop_set_all)
    return [comp for comp in comps if comp[1]]

def loop_inner_loops (p, head):
    k = ('inner_loop_set', head)
    if k in p.cached_analysis:
        return p.cached_analysis[k]
    res = loop_body_inner_loops (p, head, p.loop_body (head))
    p.cached_analysis[k] = res
    return res

def loop_heads_including_inner (p):
    heads = p.loop_heads ()
    check = [(head, p.loop_body (head)) for head in heads]
    while check:
        (head, body) = check.pop ()
        comps = loop_body_inner_loops (p, head, body)
        heads.extend ([head for (head, _) in comps])
        check.extend ([(head, [head] + list (body))
                       for (head, body) in comps])
    return heads

def check_no_inner_loop (p, head):
    subs = loop_inner_loops (p, head)
    if subs:
        printout ('Aborting %s, complex loop' % p.name)
        trace ('  sub-loops %s of loop at %s' % (subs, head))
        for (h, _) in subs:
            trace ('    head %d tagged %s' % (h, p.node_tags[h]))
        raise Abort ()

def has_inner_loop (p, head):
    return bool (loop_inner_loops (p, head))

def fun_has_inner_loop (f):
    p = f.as_problem (Problem)
    p.do_analysis ()
    return bool ([head for head in p.loop_heads ()
                  if has_inner_loop (p, head)])

def loop_var_analysis (p, head, tail):
    # getting the set of variables that go round the loop
    nodes = set (tail)
    nodes.add (head)
    used_vs = set ([])
    created_vs_at = {}
    visit = []

    def process_node (n, created):
        if p.nodes[n].is_noop ():
            lvals = set ([])
        else:
            vs = syntax.get_node_rvals (p.nodes[n])
            for rv in vs.iteritems ():
                if rv not in created:
                    used_vs.add (rv)
            lvals = set (p.nodes[n].get_lvals ())

        created = set.union (created, lvals)
        created_vs_at[n] = created

        visit.extend (p.nodes[n].get_conts ())

    process_node (head, set ([]))

    while visit:
        n = visit.pop ()
        if (n not in nodes) or (n in created_vs_at):
            continue
        if not all ([pr in created_vs_at for pr in p.preds[n]]):
            continue

        pre_created = [created_vs_at[pr] for pr in p.preds[n]]
        process_node (n, set.union (* pre_created))

    final_pre_created = [created_vs_at[pr] for pr in p.preds[head]
                         if pr in nodes]
    created = set.union (* final_pre_created)

    loop_vs = set.intersection (created, used_vs)
    trace ('Loop vars at head: %s' % loop_vs)

    return loop_vs


