"""CEGAR on the N-K4 point model (w8sat.py).  Start: base K4 + chosen witness singles.  Loop: solve; for the
solution, find core 4-sets B such that NO further edge avoiding B is consistent with the (fixed) solution; add a
generic edge avoiding the first such B (tau >= 5 says one exists) and repeat.  UNSAT => contradiction (all
constraints are TRUE consequences, see w8sat.py docstring).  Usage: w8cegar.py PAT SEL [tt] [maxit=N]"""
import sys, itertools, time, json
from w8sat import *
pat = sys.argv[1]; selarg = sys.argv[2]; flags = sys.argv[3:]
core_pts, _ = base(PAT[pat]); Wall = witnesses(core_pts)
sel = None if selarg == 'all' else ([] if selarg == 'none' else [int(t) for t in selarg.split(',')])
maxit = int(next((f.split('=')[1] for f in flags if f.startswith('maxit=')), 40))
tt = 'tt' in flags
core = [p[0] for p in core_pts]
gens = []
for it in range(maxit):
    t0 = time.time()
    e, X, pts, W = build(pat, sel, gen=gens + [()], tt=tt)
    s = Cadical153(bootstrap_with=e.cl)
    Gs = X[-1]; Xm = X[:-1]
    # solve the model without the probe edge constraints mattering: the probe edge is generic and always satisfiable
    r = s.solve()
    print(f'it {it}: edges={len(Xm)} gens={gens} -> {"SAT" if r else "UNSAT"} ({time.time()-t0:.0f}s)', flush=True)
    if not r: break
    m = set(l for l in s.get_model() if l > 0)
    fix = [(v if v in m else -v) for F in Xm for v in F['b']]
    nm = {a: pts[a][0] for a in range(len(pts))}
    bad = []
    for B in itertools.combinations(range(len(core)), 4):
        if not s.solve(assumptions=fix + [-Gs['b'][a] for a in B]): bad.append(tuple(core[a] for a in B))
    print(f'   unavoidable core 4-sets for this solution: {len(bad)}', bad[:8], flush=True)
    if not bad:
        print('   STALL: solution admits an avoiding edge for every core 4-set', flush=True)
        for F in Xm: print('   ', F['pair'], nm[F['x']] if F['x'] is not None else F['gen'], [nm[a] for a in range(len(pts)) if F['b'][a] in m], flush=True)
        break
    gens.append(bad[0])
