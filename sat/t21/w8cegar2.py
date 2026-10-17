"""CEGAR v2 on the N-K4 point model (w8sat.py): like w8cegar.py, but the probe for 'is there an edge avoiding B,
given the current solution' runs on a small model in which the solution's edges are constants; up to K new
generic edges (for distinct unavoidable core 4-sets) are added per iteration.
Usage: w8cegar2.py PAT SEL [tt] [maxit=N] [k=K] [init=json-list-of-avoid-sets]"""
import sys, itertools, time, json
from w8sat import *
pat = sys.argv[1]; selarg = sys.argv[2]; flags = sys.argv[3:]
opt = dict(f.split('=', 1) for f in flags if '=' in f)
core_pts, _ = base(PAT[pat]); core = [p[0] for p in core_pts]
sel = None if selarg == 'all' else ([] if selarg == 'none' else [int(t) for t in selarg.split(',')])
maxit = int(opt.get('maxit', 40)); K = int(opt.get('k', 3)); tt = 'tt' in flags
gens = [tuple(g) for g in json.loads(opt.get('init', '[]'))]
for it in range(maxit):
    t0 = time.time()
    e, X, pts, W = build(pat, sel, gen=gens, tt=tt)
    s = Cadical153(bootstrap_with=e.cl); r = s.solve()
    print(f'it {it}: edges={len(X)} gens={len(gens)} -> {"SAT" if r else "UNSAT"} ({time.time()-t0:.0f}s)', flush=True)
    if not r:
        print('FINAL gens =', json.dumps(gens), flush=True); break
    m = set(l for l in s.get_model() if l > 0)
    sol = [frozenset(pts[a][0] for a in range(len(pts)) if F['b'][a] in m) for F in X]
    del s, e
    t1 = time.time()
    pe, PX, _, _ = build(pat, [], gen=[()], fixed=sol, tt=tt)
    ps = Cadical153(bootstrap_with=pe.cl); G = PX[-1]
    bad = [B for B in itertools.combinations(range(len(core)), 4) if not ps.solve(assumptions=[-G['b'][a] for a in B])]
    bad = [tuple(core[a] for a in B) for B in bad]
    print(f'   probe {time.time()-t1:.0f}s: unavoidable core 4-sets: {len(bad)}', bad[:6], flush=True)
    if not bad:
        print('   STALL; solution:', flush=True)
        for F, S_ in zip(X, sol): print('   ', F['pair'], pts[F['x']][0] if F['x'] is not None else F.get('gen'), sorted(S_), flush=True)
        break
    chosen = []
    for B in bad:
        if all(len(set(B) & set(C)) <= 2 for C in chosen): chosen.append(B)
        if len(chosen) >= K: break
    gens += chosen
    print('   gens now', json.dumps(gens), flush=True)
