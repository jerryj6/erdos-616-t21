"""Check of Lemma G (hand-derived, Wave 8): in a (3,2,1,1)-K4, a (P2,P3)-single F of type y in gamma with v notin F
contains w, a3, c3, exactly one a4 point and exactly one m3 point, has F&O0 = {}, |F&O2| = 1, |F&(c4 u O1)| = 1.
(Symmetric: w notin F => v, a4, c4, one a3 point, one m3 point, F&O0 = {}, |F&O3| = 1, |F&(c3 u O1)| = 1.)
Exhaustive over all traces allowed by the base-only constraints (w8enum logic)."""
import itertools
from w8k4 import base, witnesses, PAT
pts, Osz = base(PAT['3211']); n = len(pts); nm = [p[0] for p in pts]
idx = {s: i for i, s in enumerate(nm)}
inP = lambda a, i: i in pts[a][1]
v, w = idx['T012_0'], idx['T013_0']; a3 = [idx['p02_0'], idx['p02_1']]; a4 = [idx['p03_0'], idx['p03_1']]
c3, c4 = idx['p12_0'], idx['p13_0']; m3 = [idx[f'p01_{i}'] for i in range(3)]
tot = ok = 0
for y in [idx[f'T123_{i}'] for i in range(3)]:
    i, j = 2, 3
    N = [a for a in range(n) if inP(a, i) and inP(a, j)]
    free = [a for a in range(n) if a not in N]
    for bits in itertools.product((0, 1), repeat=len(free)):
        b = [0] * n
        for a, t in zip(free, bits): b[a] = t
        b[y] = 1
        if not all(any(b[a] for a in range(n) if inP(a, k) and inP(a, l)) for k, l in itertools.combinations(range(4), 2)): continue
        core = lambda k: sum(b[a] for a in range(n) if inP(a, k))
        oi, oj = 5 - core(2), 5 - core(3)
        if oi < 0 or oj < 0: continue
        for o0 in range(0, Osz[0] + 1):
            for o1 in range(0, Osz[1] + 1):
                o = [o0, o1, oi, oj]
                if any(core(k) + o[k] < 5 for k in range(4)) or sum(b) + sum(o) > 21: continue
                good = True
                for T, t in PAT['3211'].items():
                    if any(b[a] for a in range(n) if pts[a][1] == frozenset(T)): continue
                    if sum(b[a] for a in range(n) if pts[a][1] & set(T)) + sum(o[q] for q in T) > 8 + t: good = False; break
                if not good: continue
                for (xv, xw, A3, A4, C3, C4, Oa, Ob) in ((v, w, a3, a4, c3, c4, 2, 3), (w, v, a4, a3, c4, c3, 3, 2)):
                    if b[xv]: continue
                    tot += 1
                    cond = (b[xw] and all(b[a] for a in A3) and b[C3] and sum(b[a] for a in A4) == 1 and sum(b[a] for a in m3) == 1
                            and o0 == 0 and o[Oa] == 1 and b[C4] + o1 == 1)
                    ok += bool(cond)
                    if not cond: print('COUNTEREXAMPLE', [nm[a] for a in range(n) if b[a]], o)
print('Lemma G instances', tot, 'satisfied', ok)
