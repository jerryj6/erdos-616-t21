"""Venn-region CEGAR for Erdos #616 at r=21 (tau>=5 vs L_21).
A configuration = k edges E_0..E_{k-1}; variables c_T (T nonempty bitmask over edges) = #vertices whose
edge-membership is exactly T.  Constraints (all are TRUE consequences for any counterexample G):
  * |E_i| = 21;  |E_i & E_j| >= 5 (Lemma A);  |E_0 & E_1| = 5 (Lemma A: a 5-pair exists; WLOG edges 0,1).
  * L: every subfamily I (|I|>=2) has a common vertex or union >= 61.
  * witness implications: edge j (j>=2) was created for a 'cover pattern' = multiset of regions R over the
    first j edges: IF each region R has >= mult(R) vertices THEN edge j avoids >= mult(R) of them
    (choose those vertices as a 4-set B; tau>=5 gives an edge avoiding B).  If the antecedent fails the
    solver may make edge j a copy of edge 0, which is harmless, so no false contradiction is introduced.
If the model is INFEASIBLE, no counterexample exists (proof, modulo this script).  If a solution has
covering number >= 5 *as a k-edge hypergraph*, it is a genuine counterexample (L checked on all subfamilies).
"""
import sys, itertools, time, json
from ortools.sat.python import cp_model
R, WIN = 21, 61

def restrict(T, j):
    return T & ((1 << j) - 1)

def solve(k, pats, timelimit=100, extra=None):
    m = cp_model.CpModel()
    full = 1 << k
    c = [None] + [m.NewIntVar(0, R, f'c{T}') for T in range(1, full)]
    for i in range(k):
        m.Add(sum(c[T] for T in range(1, full) if T >> i & 1) == R)
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = sum(c[T] for T in range(1, full) if T & I == I)
        m.Add(e >= 5)
        if (i, j) == (0, 1): m.Add(e == 5)
    for I in range(1, full):
        if bin(I).count('1') < 3: continue
        b = m.NewBoolVar('')
        m.Add(sum(c[T] for T in range(1, full) if T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(sum(c[T] for T in range(1, full) if T & I) >= WIN).OnlyEnforceIf(b.Not())
    for j, pat in enumerate(pats):
        e = j + 2  # edge index created by this pattern; pattern regions are masks over first e edges
        ante = []
        for Rg, mu in pat:
            a = m.NewBoolVar('')
            m.Add(sum(c[T] for T in range(1, full) if restrict(T, e) == Rg) >= mu).OnlyEnforceIf(a)
            m.Add(sum(c[T] for T in range(1, full) if restrict(T, e) == Rg) <= mu - 1).OnlyEnforceIf(a.Not())
            ante.append(a)
            m.Add(sum(c[T] for T in range(1, full) if restrict(T, e) == Rg and not (T >> e & 1)) >= mu).OnlyEnforceIf(a)
        # (if not all antecedents hold, no constraint)
        allA = m.NewBoolVar('')
        m.AddBoolAnd(ante).OnlyEnforceIf(allA)
        m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
    if extra: extra(m, c, k)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = timelimit; s.parameters.num_workers = 2
    st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return 'SAT', {T: s.Value(c[T]) for T in range(1, full) if s.Value(c[T])}
    return s.StatusName(st), None

def min_cover(k, sol, maxsize=4):
    """min multiset of regions (respecting counts) covering all k edges; returns list of (region, mult) or None"""
    regs = sorted(sol, key=lambda T: -bin(T).count('1'))
    allE = (1 << k) - 1
    for size in range(1, maxsize + 1):
        best = None
        for combo in itertools.combinations_with_replacement(regs, size):
            u = 0
            for T in combo: u |= T
            if u != allE: continue
            cnt = {}
            for T in combo: cnt[T] = cnt.get(T, 0) + 1
            if any(cnt[T] > sol[T] for T in cnt): continue
            score = sum(bin(T).count('1') for T in combo)
            if best is None or score > best[0]: best = (score, sorted(cnt.items()))
        if best: return best[1]
    return None
