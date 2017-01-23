import syntax
import target_objects

def get_cache (p):
	k = 'c_rodata_hook_cache'
	if k not in p.cached_analysis:
		p.cached_analysis[k] = {}
	return p.cached_analysis[k]

def hook (rep, (n, vc)):
	p = rep.p
	is_C = tag == 'C' or p.hook_tag_hints.get (tag, None) == 'C'
	if not is_C:
		return
	upd_ps = [ptr for (kind, ptr, v) in p.nodes[n].get_mem_accesses ()
		if kind == 'MemUpdate']
	if not upd_ps:
		return
	cache = get_cache (p)
	for ptr in upd_ps:
		pc = rep.get_pc ((n, vc))
		eq_rodata = rep.solv.get_eq_rodata_witness (ptr)
		hyp = rep.to_smt_expr (syntax.mk_implies (pc,
			syntax.mk_not (eq_rodata)), (n, vc))
		if ((n, vc), ptr) in cache:
			res = cache[((n, vc), ptr)]
		else:
			res = rep.test_hyp_whyps (hyp, [], cache = cache)
			cache[((n, vc), ptr)] = res
		if res:
			rep.solv.assert_fact (hyp, {})

module_hook_k = 'c_rodata'
target_objects.add_hook ('post_emit_node', module_hook_k, hook)

