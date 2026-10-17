"""Pruned region model: like w6model.build but region variables only for T whose restriction to the first k0 edges
lies in `base` (list of allowed k0-bit regions, 0 allowed = vertex in none of the first k0 edges).  Sound when the
first k0 edges are fully fixed by the case hypothesis (base sizes given in `basesz`)."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

def build(k, k0, basesz, pats, r=21, K=5, W=60, d1=True, maxfam=99):
    m = cp_model.CpModel(); low = (1 << k0) - 1
    regs = [T for T in range(1, 1 << k) if (T & low) in basesz]
    c = {T: m.NewIntVar(0, r, '') for T in regs}
    S = lambda pred: sum(c[T] for T in regs if pred(T))
    for b, sz in basesz.items():
        if b: m.Add(S(lambda T: (T & low) == b) == sz)
    for i in range(k0, k):
        m.Add(S(lambda T: T >> i & 1) == r)
    pairK = {}
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = S(lambda T: T & I == I); m.Add(e >= K)
        f = m.NewBoolVar(''); m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not()); pairK[(i, j)] = f
    for I in range(1, 1 << k):
        if bin(I).count('1') < 3 or bin(I).count('1') > maxfam or (I >> k0) == 0: continue
        b = m.NewBoolVar('')
        m.Add(S(lambda T: T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(S(lambda T: T & I) >= W + 1).OnlyEnforceIf(b.Not())
    if d1:
        cap = 4 * r - W - 3 * K
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l in range(k):
                if l in (i, j) or max(i, j, l) < k0: continue
                g = m.NewBoolVar('')
                miss = S(lambda T: T & I == I and not (T >> l & 1))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(S(lambda T: (T >> l & 1) and (T & I)) <= cap).OnlyEnforceIf([f, g])
    for e, pat in pats.items():
        ante = []
        for inc, exc, mu in pat:
            a = m.NewBoolVar('')
            s = S(lambda T: (T & inc) == inc and (T & exc) == 0)
            m.Add(s >= mu).OnlyEnforceIf(a); m.Add(s <= mu - 1).OnlyEnforceIf(a.Not()); ante.append(a)
        allA = m.NewBoolVar(''); m.AddBoolAnd(ante).OnlyEnforceIf(allA); m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
        for inc, exc, mu in pat:
            m.Add(S(lambda T: (T & inc) == inc and (T & exc) == 0 and not (T >> e & 1)) >= mu).OnlyEnforceIf(allA)
    return m, c, regs

def solve(k, k0, basesz, pats, tl=100, workers=2, **kw):
    t0 = time.time(); m, c, regs = build(k, k0, basesz, pats, **kw); tb = time.time() - t0
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m); name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in regs if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0, tb
