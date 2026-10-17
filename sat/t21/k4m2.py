"""Wave 7 Case N, model v2: like k4model.py but the fixed base is a list of ATOMS (refinement of the base regions,
so individual points such as each m3-point can be named).  atoms: list of (name, basemask(4 bits over P0..P3), size).
Region var c[(a, S)] = #vertices in atom a lying in exactly the new edges S (S = bitmask over new edges 0..n-1).
Same TRUE constraints as k4model.py (Lemma A, L on all subfamilies with a new edge, D1, R3a, NT).
pats[e] = list of (atomset, mu): edge e avoids >= mu points of the union of those atoms (unconditional: mu <= size);
sum mu <= 4."""
import itertools, time, sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model
from k4model import base_sizes

NAMES = {7: 'v', 11: 'w', 13: 'al', 14: 'ga', 3: 'm', 5: 'a3', 9: 'a4', 6: 'c3', 10: 'c4', 12: 'p23',
         1: 'O0', 2: 'O1', 4: 'O2', 8: 'O3', 0: 'out'}

def atoms_from(tt, split=()):
    """split: base masks whose points are made individual atoms (name+index)."""
    bs = base_sizes(tt); at = []
    for b, sz in sorted(bs.items()):
        if sz == 0 or b == 15: continue
        if b in split:
            for i in range(sz): at.append((f'{NAMES[b]}{i}', b, 1))
        else: at.append((NAMES[b], b, sz))
    at.append(('out', 0, None))
    return at

def build(n, atoms, pats, r=21, K=5, W=60, nt=True, r3a=True, d1=True):
    k = 4 + n
    m = cp_model.CpModel()
    # full mask of a region: basemask | (S << 4)
    regs = [(ai, S) for ai in range(len(atoms)) for S in range(1 << n) if not (atoms[ai][1] == 0 and S == 0)]
    c = {R: m.NewIntVar(0, r, '') for R in regs}
    full = {R: atoms[R[0]][1] | (R[1] << 4) for R in regs}
    def S(pred): return sum(c[R] for R in regs if pred(full[R], R))
    for ai, (nm, b, sz) in enumerate(atoms):
        if sz is not None: m.Add(sum(c[(ai, s)] for s in range(1 << n)) == sz)
    for i in range(4, k):
        m.Add(S(lambda T, R: T >> i & 1) == r)
    pairK = {}
    bs = {}
    for nm, b, sz in atoms:
        if sz: bs[b] = bs.get(b, 0) + sz
    for i, j in itertools.combinations(range(k), 2):
        I = (1 << i) | (1 << j)
        if j < 4: pairK[(i, j)] = True; continue
        e = S(lambda T, R: T & I == I); m.Add(e >= K)
        f = m.NewBoolVar(''); m.Add(e == K).OnlyEnforceIf(f); m.Add(e >= K + 1).OnlyEnforceIf(f.Not()); pairK[(i, j)] = f
    for I in range(1, 1 << k):
        if bin(I).count('1') < 3 or (I >> 4) == 0: continue
        b = m.NewBoolVar('')
        m.Add(S(lambda T, R: T & I == I) >= 1).OnlyEnforceIf(b)
        m.Add(S(lambda T, R: T & I) >= W + 1).OnlyEnforceIf(b.Not())
    lit = lambda f: [] if f is True else [f]
    sing = {}
    for (i, j), f in pairK.items():
        I = (1 << i) | (1 << j)
        for l in range(k):
            if l in (i, j): continue
            if max(i, j, l) < 4:
                sing[(i, j, l)] = (bs.get(I | (1 << l), 0) == 1); continue
            inter = S(lambda T, R: T & I == I and T >> l & 1)
            s = m.NewBoolVar(''); m.Add(inter == 1).OnlyEnforceIf(s); m.Add(inter != 1).OnlyEnforceIf(s.Not())
            sing[(i, j, l)] = s
            if d1:
                g = m.NewBoolVar('')
                miss = S(lambda T, R: T & I == I and not (T >> l & 1))
                m.Add(miss >= 1).OnlyEnforceIf(g); m.Add(miss == 0).OnlyEnforceIf(g.Not())
                m.Add(S(lambda T, R: (T >> l & 1) and (T & I)) <= 4 * r - W - 3 * K).OnlyEnforceIf(lit(f) + [g])
            if r3a:
                for q in (i, j):
                    Q = (1 << q) | (1 << l)
                    m.Add(S(lambda T, R: T & Q == Q) == K).OnlyEnforceIf(lit(f) + [s])
    if nt:
        for (i, j), f in pairK.items():
            I = (1 << i) | (1 << j)
            for l1, l2 in itertools.combinations([x for x in range(k) if x not in (i, j)], 2):
                if max(i, j, l1, l2) < 4: continue
                s1, s2 = sing[(i, j, l1)], sing[(i, j, l2)]
                if s1 is False or s2 is False: continue
                L = (1 << l1) | (1 << l2)
                d = m.NewBoolVar('')
                x = S(lambda T, R: T & (I | L) == (I | L))
                m.Add(x == 0).OnlyEnforceIf(d); m.Add(x >= 1).OnlyEnforceIf(d.Not())
                cond = lit(f) + [z for z in (s1, s2) if z is not True] + [d]
                for q, o in ((i, j), (j, i)):
                    m.Add(S(lambda T, R: T & (L | (1 << q)) == (L | (1 << q)) and not (T >> o & 1)) >= 2).OnlyEnforceIf(cond)
    for e, pat in pats.items():
        assert sum(mu for _, mu in pat) <= 4
        for aset, mu in pat:
            m.Add(sum(c[(ai, s)] for ai in aset for s in range(1 << n) if not (s >> (e - 4) & 1)) >= mu)
    return m, c, regs

def solve(n, atoms, pats, tl=100, workers=2, **kw):
    t0 = time.time(); m, c, regs = build(n, atoms, pats, **kw)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m); name = s.StatusName(st)
    sol = {R: s.Value(c[R]) for R in regs if s.Value(c[R])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0

def show(n, atoms, sol):
    out = {}
    for (ai, S), v in sol.items():
        out.setdefault(atoms[ai][0], []).append((''.join('1' if S >> e & 1 else '0' for e in range(n)), v))
    return out

def A(atoms, *names):
    return [i for i, a in enumerate(atoms) if a[0] in names]
