"""Wave 7 Case N: region model with a fixed K4 configuration as base.
Base edges P0..P3 (bits 0..3), pairwise |Pi&Pj| = 5, empty 4-fold intersection, triple sizes tt[l] = |cap_{i!=l} Pi|
(sum 7).  Pair-private p_ij = 5 - t_ijk - t_ijl, outside O_i = 21 - sum(triples containing i) - sum_j p_ij.
New edges 4..k-1.  Region c[T] for T (k-bit mask) whose low 4 bits are a nonempty-base region or 0 (outside).
TRUE constraints at r=21 used (all proved in candidates/erdos-616-t21-upper.md section 1/6):
  |E|=21; |Ei&Ej|>=5 (Lemma A); L on every subfamily (>=3 edges, containing a new edge);
  D1: (i,j) 5-pair, M_ij not inside E_l  ->  |E_l & (E_i|E_j)| <= 9;
  R3a: (i,j) 5-pair, |E_k & M_ij| = 1  ->  |E_k & E_i| = |E_k & E_j| = 5   (R.2+R.3: singles of >=2 types exist);
  NT (Case N hypothesis, no triangle): (i,j) 5-pair, k,l singles of (i,j) of different types
      -> |E_k&E_l&(E_i\\E_j)| >= 2 and |E_k&E_l&(E_j\\E_i)| >= 2   (this also contains Lemma S(c)).
Witness patterns: pats[e] = list of (pred, mu): pred(T) on regions of earlier edges; if all groups have >= mu
points then edge e avoids >= mu points of each group (sum mu <= 4, tau >= 5).
INFEASIBLE => the hypothesised configuration cannot occur in a counterexample."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

def base_sizes(tt, r=21):
    # tt[l] = size of triple intersection of the three P's other than P_l
    sz = {}
    for l in range(4):
        sz[15 ^ (1 << l)] = tt[l]
    for i, j in itertools.combinations(range(4), 2):
        k, l = [x for x in range(4) if x not in (i, j)]
        sz[(1 << i) | (1 << j)] = 5 - tt[l] - tt[k]
    for i in range(4):
        sz[1 << i] = r - sum(tt[l] for l in range(4) if l != i) - sum(5 - tt[l] - tt[k]
                     for j in range(4) if j != i for k, l in [tuple(x for x in range(4) if x not in (i, j))])
    sz[15] = 0
    assert all(v >= 0 for v in sz.values()), sz
    return sz

def build(k, tt, pats, r=21, K=5, W=60, nt=True, r3a=True, d1=True, extra=None):
    bs = base_sizes(tt, r)
    allowed = [b for b, v in bs.items() if v > 0] + [0]
    m = cp_model.CpModel()
    regs = [T for T in range(1, 1 << k) if (T & 15) in allowed]
    c = {T: m.NewIntVar(0, r, '') for T in regs}
    S = lambda pred: sum(c[T] for T in regs if pred(T))
    for b in allowed:
        if b: m.Add(S(lambda T: (T & 15) == b) == bs[b])
    for i in range(4, k):
        m.Add(S(lambda T: T >> i & 1) == r)
    pairK = {}
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        e = S(lambda T: T & I == I)
        if j < 4:
            pairK[(i, j)] = True; continue
        m.Add(e >= K)
        f = m.NewBoolVar(''); m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not()); pairK[(i, j)] = f
    for I in range(1, 1 << k):
        if bin(I).count('1') < 3 or (I >> 4) == 0: continue
        b = m.NewBoolVar('')
        m.Add(S(lambda T: T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(S(lambda T: T & I) >= W + 1).OnlyEnforceIf(b.Not())
    lit = lambda f: [] if f is True else [f]
    # singles indicator s[(i,j,l)] : |E_l & M_ij| == 1
    sing = {}
    for (i, j), f in pairK.items():
        I = (1 << i) | (1 << j)
        for l in range(k):
            if l in (i, j): continue
            inter = S(lambda T: T & I == I and T >> l & 1)
            if max(i, j, l) < 4:
                sing[(i, j, l)] = (bs[I | (1 << l)] == 1); continue
            s = m.NewBoolVar(''); m.Add(inter == 1).OnlyEnforceIf(s); m.Add(inter != 1).OnlyEnforceIf(s.Not())
            sing[(i, j, l)] = s
            if d1:
                g = m.NewBoolVar('')
                miss = S(lambda T: T & I == I and not (T >> l & 1))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(S(lambda T: (T >> l & 1) and (T & I)) <= 4 * r - W - 3 * K).OnlyEnforceIf(lit(f) + [g])
            if r3a:
                for q in (i, j):
                    Q = (1 << q) | (1 << l)
                    m.Add(S(lambda T: T & Q == Q) == K).OnlyEnforceIf(lit(f) + [s])
    if nt:
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l1, l2 in itertools.combinations([x for x in range(k) if x not in (i, j)], 2):
                if max(i, j, l1, l2) < 4: continue
                s1, s2 = sing[(i, j, l1)], sing[(i, j, l2)]
                if s1 is False or s2 is False: continue
                L = (1 << l1) | (1 << l2)
                d = m.NewBoolVar('')  # different types: E_l1 & E_l2 & M_ij empty
                x = S(lambda T: T & (I | L) == (I | L))
                m.Add(x == 0).OnlyEnforceIf(d); m.Add(x >= 1).OnlyEnforceIf(d.Not())
                cond = lit(f) + [z for z in (s1, s2) if z is not True] + [d]
                for q, o in ((i, j), (j, i)):
                    m.Add(S(lambda T: T & (L | (1 << q)) == (L | (1 << q)) and not (T >> o & 1)) >= 2).OnlyEnforceIf(cond)
    for e, pat in pats.items():
        ante = []
        for pred, mu in pat:
            a = m.NewBoolVar('')
            s_ = S(lambda T: pred(T & ((1 << e) - 1)))
            m.Add(s_ >= mu).OnlyEnforceIf(a); m.Add(s_ <= mu - 1).OnlyEnforceIf(a.Not()); ante.append(a)
        allA = m.NewBoolVar(''); m.AddBoolAnd(ante).OnlyEnforceIf(allA); m.AddBoolOr([x.Not() for x in ante]).OnlyEnforceIf(allA.Not())
        for pred, mu in pat:
            m.Add(S(lambda T: pred(T & ((1 << e) - 1)) and not (T >> e & 1)) >= mu).OnlyEnforceIf(allA)
    if extra: extra(m, c, regs, S)
    return m, c, regs

def solve(k, tt, pats, tl=100, workers=2, **kw):
    t0 = time.time(); m, c, regs = build(k, tt, pats, **kw); tb = time.time() - t0
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m); name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in regs if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0, tb

def show(k, sol):
    return {bin(T)[2:].zfill(k)[::-1]: v for T, v in sorted(sol.items())}

def reg(b):  # predicate: vertex lies in base region b (any membership in earlier new edges)
    return lambda T: (T & 15) == b
