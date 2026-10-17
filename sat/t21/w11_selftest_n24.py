"""Encoding control for the new N24 kind: fix every edge bit to a literal realization; a violated N24 instance must make
the model UNSAT, a satisfied one must keep it SAT.  python3 w11_selftest_n24.py REAL.json CK.json"""
import sys, json, itertools, random
sys.path.append('.')
from w10x_exact import Exact, setup, check
real = json.load(open(sys.argv[1])); st = json.load(open(sys.argv[2]))
br = st['branch']; names, B, nk, edges, K, Kb = setup(br, st['opt'])
md0 = Exact(names, B, edges, K, nk, solver=False); md0.no24 = True
ix = {nm: i for i, nm in enumerate(md0.names)}
sol = [frozenset(ix[p] for p in real['edges'][4 + q] if p in ix) for q in range(len(edges))]
v = [z for z in check(md0, sol) if z[0] == 'N24']
print('N24 violations of the realization:', len(v), v[:4])
# satisfied instances: all cross-type single pairs at 5-pairs of the realization that are NOT (2,4)
E = [frozenset(b) for b in B] + [s | frozenset(('p', q, i) for i in range(21 - len(s))) for q, s in enumerate(sol)]
nb = 4; idx = lambda k: -1 - k if k < nb else k - nb
sat = []
for i, j in itertools.combinations(range(len(E)), 2):
    N = E[i] & E[j]
    if len(N) != 5: continue
    sg = [(k, next(iter(E[k] & N))) for k in range(len(E)) if k not in (i, j) and len(E[k] & N) == 1]
    for (a, t1), (b, t2) in itertools.combinations(sg, 2):
        if t1 != t2 and ['N24', idx(i), idx(j), idx(a), idx(b)] not in v: sat.append(['N24', idx(i), idx(j), idx(a), idx(b)])
random.seed(1); tests = [(z, False) for z in v[:6]] + [(z, True) for z in random.sample(sat, min(6, len(sat)))]
bad = 0
for z, expect in tests:
    md = Exact(names, B, edges, K, nk)
    for q, e in enumerate(md.edges):
        for a in range(md.n): md.add([e['x'][a] if a in sol[q] else -e['x'][a]], 'FIX')
    md.add_inst(z); r = md.solver.solve(); md.solver.delete()
    ok = (bool(r) == expect); bad += not ok
    print(z, 'expect', 'SAT' if expect else 'UNSAT', 'got', 'SAT' if r else 'UNSAT', 'OK' if ok else 'MISMATCH', flush=True)
print('mismatches', bad, 'of', len(tests))
