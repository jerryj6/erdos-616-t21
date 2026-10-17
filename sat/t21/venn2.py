"""Venn-region model v2 (group patterns).  See venn_cegar.py docstring for soundness.
pattern for edge e = list of (inc, exc, mu): group = vertices lying in every edge of inc and in no edge of exc
(inc, exc are bitmasks over edges < e).  Constraint: IF |group| >= mu for every item THEN edge e avoids >= mu
vertices of each group (pick those vertices as the 4-set B, sum of mu <= 4; tau>=5 gives the edge)."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model
R, WIN = 21, 61

def build(k, pats, five_pair=True, extra=None):
    m = cp_model.CpModel(); full = 1 << k
    c = [None] + [m.NewIntVar(0, R, f'c{T}') for T in range(1, full)]
    for i in range(k):
        m.Add(sum(c[T] for T in range(1, full) if T >> i & 1) == R)
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = sum(c[T] for T in range(1, full) if T & I == I)
        m.Add(e >= 5)
        if five_pair and (i, j) == (0, 1): m.Add(e == 5)
    for I in range(1, full):
        if bin(I).count('1') < 3: continue
        b = m.NewBoolVar('')
        m.Add(sum(c[T] for T in range(1, full) if T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(sum(c[T] for T in range(1, full) if T & I) >= WIN).OnlyEnforceIf(b.Not())
    for e, pat in pats.items():
        assert sum(it[2] for it in pat) <= 4
        msk = (1 << e) - 1
        ante = []
        for item in pat:
            inc, exc, mu = item[:3]; exact = len(item) > 3 and item[3]
            assert (inc | exc) <= msk
            grp = [T for T in range(1, full) if (T & inc) == inc and (T & exc) == 0]
            a = m.NewBoolVar('')
            if exact:
                a1 = m.NewBoolVar(''); a2 = m.NewBoolVar('')
                m.Add(sum(c[T] for T in grp) >= mu).OnlyEnforceIf(a1)
                m.Add(sum(c[T] for T in grp) <= mu - 1).OnlyEnforceIf(a1.Not())
                m.Add(sum(c[T] for T in grp) <= mu).OnlyEnforceIf(a2)
                m.Add(sum(c[T] for T in grp) >= mu + 1).OnlyEnforceIf(a2.Not())
                m.AddBoolAnd([a1, a2]).OnlyEnforceIf(a)
                m.AddBoolOr([a1.Not(), a2.Not()]).OnlyEnforceIf(a.Not())
            else:
                m.Add(sum(c[T] for T in grp) >= mu).OnlyEnforceIf(a)
                m.Add(sum(c[T] for T in grp) <= mu - 1).OnlyEnforceIf(a.Not())
            ante.append(a)
        allA = m.NewBoolVar('')
        m.AddBoolAnd(ante).OnlyEnforceIf(allA)
        m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
        for item in pat:
            inc, exc, mu = item[:3]
            grp = [T for T in range(1, full) if (T & inc) == inc and (T & exc) == 0 and not (T >> e & 1)]
            m.Add(sum(c[T] for T in grp) >= mu).OnlyEnforceIf(allA)
    if extra: extra(m, c, k)
    return m, c

def run(k, pats, tl=100, **kw):
    t0 = time.time()
    m, c = build(k, pats, **kw)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 2
    st = s.Solve(m)
    name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in range(1, 1 << k) if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0

def show(k, sol):
    return {bin(T)[2:].zfill(k)[::-1]: v for T, v in sorted(sol.items())}
B = lambda *idx: sum(1 << i for i in idx)
