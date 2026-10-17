"""Wave 6 region model (generic in r, K=tau target, W=window).  Edges 0..k-1; c[T] = #vertices whose membership
set among the k edges is exactly T.  Constraints (all TRUE consequences in any counterexample G):
  size r; pairs >= K (L1); pair (0,1) == K (Lemma A); L on every subfamily (>=3 edges);
  D1 (needs the tight rigidity, valid at r=21 and the r=16 analogue, NOT at r=22): if |E_i & E_j| == K and
     E_l does not contain M_ij = E_i & E_j, then |E_l & (E_i | E_j)| <= 4r - W - 3K   (=9 at r=21, =7 at r=16).
  witness patterns: pats[e] = list of (inc, exc, mu) over edges < e: IF every group has >= mu vertices THEN edge e
     avoids >= mu vertices of each group (a <=4-set exists; tau>=5 gives an edge avoiding it).
  fixed: list of (inc, exc, op, val) constraints on group sizes over ALL k edges (case hypotheses).
INFEASIBLE => no counterexample containing the hypothesised configuration."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

def grp(k, inc, exc, without=None):
    full = 1 << k
    return [T for T in range(1, full) if (T & inc) == inc and (T & exc) == 0 and (without is None or not (T >> without & 1))]

def build(k, pats, fixed=(), r=21, K=5, W=60, d1=True, five01=True):
    m = cp_model.CpModel(); full = 1 << k
    c = [None] + [m.NewIntVar(0, r, f'c{T}') for T in range(1, full)]
    S = lambda Ts: sum(c[T] for T in Ts)
    for i in range(k):
        m.Add(S(grp(k, 1 << i, 0)) == r)
    pairK = {}
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = S(grp(k, I, 0)); m.Add(e >= K)
        if five01 and (i, j) == (0, 1): m.Add(e == K)
        f = m.NewBoolVar(f'f{i}{j}')
        m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not())
        pairK[(i, j)] = f
    for I in range(1, full):
        if bin(I).count('1') < 3: continue
        b = m.NewBoolVar('')
        m.Add(S(grp(k, I, 0)) >= 1).OnlyEnforceIf(b)
        m.Add(sum(c[T] for T in range(1, full) if T & I) >= W + 1).OnlyEnforceIf(b.Not())
    if d1:
        cap = 4 * r - W - 3 * K
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l in range(k):
                if l in (i, j): continue
                g = m.NewBoolVar('')  # g <=> M_ij not contained in E_l
                miss = S(grp(k, I, 1 << l))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(sum(c[T] for T in range(1, full) if (T >> l & 1) and (T & I)) <= cap).OnlyEnforceIf([f, g])
    for e, pat in pats.items():
        assert sum(it[2] for it in pat) <= 4
        ante = []
        for inc, exc, mu in pat:
            assert (inc | exc) < (1 << e)
            a = m.NewBoolVar('')
            m.Add(S(grp(k, inc, exc)) >= mu).OnlyEnforceIf(a)
            m.Add(S(grp(k, inc, exc)) <= mu - 1).OnlyEnforceIf(a.Not())
            ante.append(a)
        allA = m.NewBoolVar('')
        m.AddBoolAnd(ante).OnlyEnforceIf(allA)
        m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
        for inc, exc, mu in pat:
            m.Add(S(grp(k, inc, exc, without=e)) >= mu).OnlyEnforceIf(allA)
    for inc, exc, op, val in fixed:
        s = S(grp(k, inc, exc))
        if op == '==': m.Add(s == val)
        elif op == '>=': m.Add(s >= val)
        elif op == '<=': m.Add(s <= val)
    return m, c

def solve(k, pats, fixed=(), tl=100, workers=2, **kw):
    t0 = time.time()
    m, c = build(k, pats, fixed, **kw)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m)
    name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in range(1, 1 << k) if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0

def show(k, sol):
    return {bin(T)[2:].zfill(k)[::-1]: v for T, v in sorted(sol.items())}

def min_cover(k, sol, maxsize=4):
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

B = lambda *idx: sum(1 << i for i in idx)
