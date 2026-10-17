"""Enumerate, for each witness class of the K4, all core traces (+ |F&O_i| counts) of a single that satisfy the
base-only TRUE constraints: Lemma A vs P_k, R3 (|F&P_i|=|F&P_j|=5, F&N_ij={x}), F1 (F meets every N_kl),
L3 ({P_i,P_j,P_k,F}, F avoiding T_ijk => |F&(Pi u Pj u Pk)| <= 8+t)."""
import itertools, sys, collections
from w8k4 import base, witnesses, PAT
pat = sys.argv[1]
pts, Osz = base(PAT[pat]); n = len(pts)
W = witnesses(pts)
inP = lambda a, i: i in pts[a][1]
res = {}
for (i, j, x) in W:
    N = [a for a in range(n) if inP(a, i) and inP(a, j)]
    free = [a for a in range(n) if a not in N]
    sols = []
    for bits in itertools.product((0, 1), repeat=len(free)):
        b = [0] * n
        for a, v in zip(free, bits): b[a] = v
        b[x] = 1
        core = lambda k: sum(b[a] for a in range(n) if inP(a, k))
        ok = all(any(b[a] for a in range(n) if inP(a, k) and inP(a, l)) for k, l in itertools.combinations(range(4), 2))
        if not ok: continue
        # O counts: o_i, o_j fixed by =5 ; o_k,o_l >= 5-core
        oi, oj = 5 - core(i), 5 - core(j)
        if oi < 0 or oj < 0 or oi > Osz[i] or oj > Osz[j]: continue
        k, l = [t for t in range(4) if t not in (i, j)]
        for ok_ in range(max(0, 5 - core(k)), Osz[k] + 1):
            for ol in range(max(0, 5 - core(l)), Osz[l] + 1):
                o = [0] * 4; o[i], o[j], o[k], o[l] = oi, oj, ok_, ol
                if sum(b) + sum(o) > 21: continue
                good = True
                for T, t in PAT[pat].items():
                    if any(b[a] for a in range(n) if pts[a][1] == frozenset(T)): continue
                    if sum(b[a] for a in range(n) if pts[a][1] & set(T)) + sum(o[q] for q in T) > 8 + t: good = False; break
                if good: sols.append((tuple(b), tuple(o)))
    res[(i, j, x)] = sols
    # summarise forced points
    names = [pts[a][0] for a in range(n)]
    forced_in = [names[a] for a in range(n) if all(s[0][a] for s in sols)]
    forced_out = [names[a] for a in range(n) if not any(s[0][a] for s in sols)]
    print((i, j, names[x]), 'nsol', len(sols), 'traces', len({s[0] for s in sols}), 'in:', forced_in, 'out:', forced_out,
          'omax', [max(s[1][q] for s in sols) if sols else None for q in range(4)], flush=True)
