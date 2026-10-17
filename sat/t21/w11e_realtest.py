r"""SOUNDNESS CONTROL: a literally verified configuration (w11_TAG_real.json, checked by w10x_verify.py) must satisfy the
master CNF of TAG built WITHOUT symmetry breaking plus EVERY applicable Benders cut (both pools + symmetric images).
python3 w11e_realtest.py TAG REALFILE      -> SAT expected; UNSAT would expose an unsound encoded constraint."""
import sys, os, json, time
sys.path.insert(0, '.'); sys.path.insert(0, '../pylib')
from w8sat import build
import w11_benders as WB, w11e_sub as ES
from pysat.solvers import Cadical153
tag, realf = sys.argv[1], sys.argv[2]
meta = json.load(open(f'w11s_{tag}_meta.json')); sel = meta['sel']
t = time.time(); e, X, pts, W = build('3211', sel=sel, tt=True, sb=False, extra=WB.l4a_extra)
names = [p[0] for p in pts]; assert names == meta['names']
bvars = [F['b'] for F in X]; base = [sum(1 << a for a in range(61) if k in pts[a][1]) for k in range(4)]
m2 = dict(top=e.pool.top, T=e.T); f2l = {s['full']: l for l, s in enumerate(meta['slots'])}
enc, cc, used = ES.rebuild(m2, bvars, base, f2l)
print(f'base (no SB) {len(e.cl)} clauses, cuts {len(cc)} clauses from {used} certificates ({time.time()-t:.0f}s)', flush=True)
d = json.load(open(realf)); E = [frozenset(x) for x in d['edges']]
assert [sorted(E[k]) for k in range(4)] == [sorted(a for a in range(61) if k in pts[a][1]) for k in range(4)], 'base edges differ'
ass = []
for l in range(len(X)):
    tr = E[4 + l] & frozenset(range(61))
    ass += [bvars[l][a] if a in tr else -bvars[l][a] for a in range(61)]
s = Cadical153(bootstrap_with=e.cl + cc)
r = s.solve(assumptions=ass)
print('realized configuration vs base(noSB)+all cuts:', 'SAT (consistent)' if r else 'UNSAT  <-- SOUNDNESS PROBLEM')
if not r:
    s2 = Cadical153(bootstrap_with=e.cl); print('   base alone:', 'SAT' if s2.solve(assumptions=ass) else 'UNSAT')
