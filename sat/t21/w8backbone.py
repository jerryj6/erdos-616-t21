import sys, time
from w8sat import *
pat = sys.argv[1]; flags = sys.argv[2:]
e, X, pts, W = build(pat, None, tt=('tt' in flags))
s = Cadical153(bootstrap_with=e.cl)
assert s.solve()
ncore = sum(1 for p in pts if not p[0].startswith('O'))
cand = {}
m = set(l for l in s.get_model() if l > 0)
for k, F in enumerate(X):
    for a in range(len(pts)):
        if pts[a][0].startswith('O'): continue
        v = F['b'][a]; cand[(k, a)] = (v in m)
t0 = time.time()
for key in list(cand):
    if key not in cand: continue
    k, a = key; v = X[k]['b'][a]; val = cand[key]
    lit = -v if val else v
    if s.solve(assumptions=[lit]):
        mm = set(l for l in s.get_model() if l > 0)
        for kk in list(cand):
            if (X[kk[0]]['b'][kk[1]] in mm) != cand[kk]: del cand[kk]
print('time', time.time() - t0)
for k, F in enumerate(X):
    fin = [pts[a][0] for a in range(len(pts)) if cand.get((k, a)) is True]
    fout = [pts[a][0] for a in range(len(pts)) if cand.get((k, a)) is False]
    print(F['pair'], pts[F['x']][0], 'IN', fin, 'OUT', fout)
