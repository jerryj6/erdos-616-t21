r"""Wave 8 N-K4 exploration model (CP-SAT).  Base: a K4 P0..P3 (pairwise |Pi&Pj|=5, empty 4-fold intersection) with
triple sizes t[ijk] (pattern (3,2,1,1) or (2,2,2,1)).  Core points (union of pairwise intersections) are named
individually; private parts O_i (|O_i| = 21 - |P_i & core|) and U (outside all P_i) are handled by counts.
New edges: the singles S^{ij}_x for every pair (i,j) and type x in N_ij that is not realised by a base edge.
Per new edge F: core bits, o[F,i] = |F&O_i|, u[F] = |F&U|.  Per pair of new edges: y[F,F',i] = |F&F'&O_i|,
yu[F,F'] = |F&F'&U| with the trivial bounds max(0,a+b-|O|) <= y <= min(a,b), 0 <= yu <= min(u,u').
TRUE constraints (consequences of L, tau>=5 in any counterexample):
 (A)  Lemma A: |F&P_i| >= 5, |F&F'| >= 5.     (R3) singles: F&N_ij = {x}, |F&P_i| = |F&P_j| = 5.
 (F1) any 3 edges share a point (for {F,P_i,P_j} and {F,F',P_i}).
 (L3) {P_i,P_j,P_k,F}, F & T_ijk = {}:  |F & (P_i u P_j u P_k)| <= 8 + t_ijk.
 (L4) {P_i,P_j,F,F'} with F&F'&N_ij = {}: union >= 61 (exact in the variables).
 (L5) {P_i,P_j,P_k,F,F'} with F&F'&T_ijk = {}: union >= 61 (uses only y,yu: exact).
 (NT) no triangle (Theorem W7-I): cross-type singles of a base pair have |A&A'| >= 2 and |C&C'| >= 2.
"""
import sys, itertools, time
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

def base_named(pattern):
    pts, Osz = base(pattern)
    for i in range(4):
        for a in range(Osz[i]): pts.append((f"O{i}_{a}", frozenset((i,))))
    return pts, [0,0,0,0]

def base(pattern):
    # pattern: dict triple(tuple sorted) -> size
    pts = []  # (name, membership frozenset)
    for T, s in pattern.items():
        for a in range(s): pts.append((f"T{''.join(map(str,T))}_{a}", frozenset(T)))
    for i, j in itertools.combinations(range(4), 2):
        p = 5 - sum(s for T, s in pattern.items() if i in T and j in T)
        assert p >= 0
        for a in range(p): pts.append((f"p{i}{j}_{a}", frozenset((i, j))))
    Osz = [21 - sum(1 for _, m in pts if i in m) for i in range(4)]
    return pts, Osz

PAT = {'3211': {(0,1,2): 1, (0,1,3): 1, (0,2,3): 2, (1,2,3): 3},
       '2221': {(0,1,2): 2, (0,1,3): 2, (0,2,3): 2, (1,2,3): 1}}

def witnesses(pts):
    W = []
    for i, j in itertools.combinations(range(4), 2):
        N = [a for a, (_, m) in enumerate(pts) if i in m and j in m]
        for x in N:
            # realised by a base edge k if P_k & N_ij = {x}
            real = any(sum(1 for b in N if k in pts[b][1]) == 1 and k in pts[x][1] for k in range(4) if k not in (i, j))
            if not real: W.append((i, j, x))
    return W

def build(patname, wsel=None, nt=True, l4=True, l5=True, extra=None, named=False, tri=False):
    pts, Osz = (base_named if named else base)(PAT[patname]); n = len(pts)
    W = witnesses(pts)
    if wsel is not None: W = [w for k, w in enumerate(W) if k in wsel]
    m = cp_model.CpModel()
    inP = lambda a, i: i in pts[a][1]
    E = []
    for (i, j, x) in W:
        b = [m.NewBoolVar(f'b{i}{j}{x}_{a}') for a in range(n)]
        o = [m.NewIntVar(0, Osz[k], '') for k in range(4)]
        u = m.NewIntVar(0, 21, '')
        m.Add(sum(b) + sum(o) + u == 21)
        F = dict(b=b, o=o, u=u, pair=(i, j), x=x)
        Pc = lambda k, F=F: sum(F['b'][a] for a in range(n) if inP(a, k)) + F['o'][k]
        F['P'] = Pc
        for k in range(4): m.Add(Pc(k) >= 5)
        N = [a for a in range(n) if inP(a, i) and inP(a, j)]
        for a in N: m.Add(b[a] == (1 if a == x else 0))
        m.Add(Pc(i) == 5); m.Add(Pc(j) == 5)
        E.append(F)
    def union_count(F, ks):  # |F & union_{k in ks} P_k|
        return sum(F['b'][a] for a in range(n) if pts[a][1] & set(ks)) + sum(F['o'][k] for k in ks)
    for F in E:
        for T, t in PAT[patname].items():
            Ts = [a for a in range(n) if pts[a][1] == frozenset(T)]
            av = m.NewBoolVar('')  # F avoids T
            m.Add(sum(F['b'][a] for a in Ts) == 0).OnlyEnforceIf(av)
            m.Add(sum(F['b'][a] for a in Ts) >= 1).OnlyEnforceIf(av.Not())
            m.Add(union_count(F, T) <= 8 + t).OnlyEnforceIf(av)
            F.setdefault('avT', {})[T] = av
        for i, j in itertools.combinations(range(4), 2):
            m.Add(sum(F['b'][a] for a in range(n) if inP(a, i) and inP(a, j)) >= 1)
    # pairs of new edges
    for e1, e2 in itertools.combinations(range(len(E)), 2):
        F, G = E[e1], E[e2]
        bb = []
        for a in range(n):
            z = m.NewBoolVar(''); m.AddMultiplicationEquality(z, [F['b'][a], G['b'][a]]); bb.append(z)
        y = []
        for k in range(4):
            yk = m.NewIntVar(0, Osz[k], ''); m.Add(yk <= F['o'][k]); m.Add(yk <= G['o'][k])
            m.Add(yk >= F['o'][k] + G['o'][k] - Osz[k]); y.append(yk)
        yu = m.NewIntVar(0, 21, ''); m.Add(yu <= F['u']); m.Add(yu <= G['u'])
        m.Add(sum(bb) + sum(y) + yu >= 5)                               # Lemma A
        for k in range(4):                                              # F1 with P_k
            m.Add(sum(bb[a] for a in range(n) if inP(a, k)) + y[k] >= 1)
        same_pair_cross = (F['pair'] == G['pair'])
        for i, j in itertools.combinations(range(4), 2):
            N = [a for a in range(n) if inP(a, i) and inP(a, j)]
            av = m.NewBoolVar('')
            m.Add(sum(bb[a] for a in N) == 0).OnlyEnforceIf(av)
            m.Add(sum(bb[a] for a in N) >= 1).OnlyEnforceIf(av.Not())
            outside = sum(bb[a] for a in range(n) if not (inP(a, i) or inP(a, j))) + sum(y[k] for k in range(4) if k not in (i, j)) + yu
            uni = 37 + (21 - union_count(F, (i, j))) + (21 - union_count(G, (i, j))) - outside
            if l4: m.Add(uni >= 61).OnlyEnforceIf(av)
            if nt and same_pair_cross and F['pair'] == (i, j):
                # A-part overlap, C-part overlap >= 2 (no triangle)
                for s, o in ((i, j), (j, i)):
                    m.Add(sum(bb[a] for a in range(n) if inP(a, s) and not inP(a, o)) + y[s] >= 2)
        if l5:
            for T, t in PAT[patname].items():
                Ts = [a for a in range(n) if pts[a][1] == frozenset(T)]
                av = m.NewBoolVar('')
                m.Add(sum(bb[a] for a in Ts) == 0).OnlyEnforceIf(av)
                m.Add(sum(bb[a] for a in Ts) >= 1).OnlyEnforceIf(av.Not())
                outside = sum(bb[a] for a in range(n) if not (pts[a][1] & set(T))) + sum(y[k] for k in range(4) if k not in T) + yu
                uni = 48 + t + (21 - union_count(F, T)) + (21 - union_count(G, T)) - outside
                m.Add(uni >= 61).OnlyEnforceIf(av)
    if tri: add_tracetri(m, E, pts, n)
    if extra: extra(m, E, pts, Osz)
    return m, E, pts, Osz, W

def add_tracetri(m, E, pts, n):
    """(TT) No trace triangle on a base edge P_i (W7-1 + Theorem W7-I): among edges X (base or new, X != P_i) with
    |X & P_i| = 5, no three whose traces on P_i pairwise meet in exactly one point and have empty common intersection.
    Only valid in the NAMED model (all points of P_i named)."""
    edges = []
    for k in range(4):
        edges.append(dict(b=[1 if k in pts[a][1] else 0 for a in range(n)], base=k))
    edges += E
    for i in range(4):
        Pi = [a for a in range(n) if i in pts[a][1]]
        X = [e for e in edges if e.get('base') != i]
        e5 = []
        for e in X:
            s5 = sum(e['b'][a] for a in Pi)
            if isinstance(s5, int): e5.append(True if s5 == 5 else False)
            else:
                f = m.NewBoolVar(''); m.Add(s5 == 5).OnlyEnforceIf(f); m.Add(s5 != 5).OnlyEnforceIf(f.Not()); e5.append(f)
        z = {}; prod = {}
        for p, q in itertools.combinations(range(len(X)), 2):
            if e5[p] is False or e5[q] is False: continue
            terms = []
            for a in Pi:
                x1, x2 = X[p]['b'][a], X[q]['b'][a]
                if isinstance(x1, int) and isinstance(x2, int): terms.append(x1 * x2)
                elif isinstance(x1, int): terms.append(x2 if x1 else 0)
                elif isinstance(x2, int): terms.append(x1 if x2 else 0)
                else:
                    t = m.NewBoolVar(''); m.AddMultiplicationEquality(t, [x1, x2]); terms.append(t)
            prod[p, q] = terms
            s1 = sum(terms)
            if isinstance(s1, int): z[p, q] = (s1 == 1)
            else:
                f = m.NewBoolVar(''); m.Add(s1 == 1).OnlyEnforceIf(f); m.Add(s1 != 1).OnlyEnforceIf(f.Not()); z[p, q] = f
        lits = lambda v: [] if v is True else [v.Not()]
        for p, q, r in itertools.combinations(range(len(X)), 3):
            if any(e5[t] is False for t in (p, q, r)): continue
            if any(z.get(pr) is False or pr not in z for pr in ((p, q), (p, r), (q, r))): continue
            if all(isinstance(X[t].get('base'), int) for t in (p, q, r)): continue
            pre = lits(e5[p]) + lits(e5[q]) + lits(e5[r]) + lits(z[p, q]) + lits(z[p, r]) + lits(z[q, r])
            for ai, a in enumerate(Pi):
                pq = prod[p, q][ai]
                if isinstance(pq, int) and pq == 0: continue
                cl = list(pre) + ([] if isinstance(pq, int) else [pq.Not()])
                xr = X[r]['b'][a]
                if isinstance(xr, int):
                    if xr == 1: continue
                else: cl.append(xr)
                m.AddBoolOr(cl)

def solve(patname, tl=100, workers=2, **kw):
    m, E, pts, Osz, W = build(patname, **kw)
    if kw.get('named'): pts = pts
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    t0 = time.time(); st = s.Solve(m)
    out = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out = []
        for F, w in zip(E, W):
            out.append((w, [pts[a][0] for a in range(len(pts)) if s.Value(F['b'][a])], [s.Value(v) for v in F['o']], s.Value(F['u'])))
    return s.StatusName(st), time.time() - t0, out, W, pts

if __name__ == '__main__':
    pat = sys.argv[1]; tl = float(sys.argv[2]) if len(sys.argv) > 2 else 100
    named = 'named' in sys.argv
    pts, Osz = base(PAT[pat]); W = witnesses(pts)
    print(pat, 'core', len(pts), 'O', Osz, 'witnesses', len(W), [(i, j, pts[x][0]) for i, j, x in W], 'named' if named else '')
    st, t, out, W, pts = solve(pat, tl=tl, named=named, tri=('tri' in sys.argv))
    print(st, f'{t:.1f}s')
    if out:
        for o in out: print(o)
