r"""Wave 8 N-noK4 exploration model (CP-SAT).  Sound relaxation of any counterexample in branch N-noK4.
Hypothesis NK (= N-noK4): for every 5-pair (X,Y), two singles of different types meet in >= 6 points.
Base: 5-pair (E1,E2), M={0..4}, A (16 pts), C (16 pts); singles F_y (type y, y=0..4) with A_y, C_y (4 each),
O_y (12 named points each, pairwise disjoint, outside E1uE2).  F_0 = G with A_0 = first 4 of A, C_0 = first 4 of C.
Optional edges ("var edges", have rest r = # points outside the 97 model points):
  WA[y,p] : Lemma-T witness of F_y at p in A_y   (WA & ({y} u A_y) = {p})
  WC[y,q] : C-side witness of F_y at q in C_y    (WC & ({y} u C_y) = {q})
  J[B]    : an edge avoiding a given 4-set B of model points (tau >= 5)
Constraints (all consequences of L, tau>=5, NK; every one sound for the real hypergraph):
  size: |Z & model| + r_Z = 21.
  Lemma A: |Z & Z'| >= 5, realised as |Z&Z'&model| + ro[Z,Z'] >= 5 with ro <= min(r,r') (rest overlap).
  L: every family of <= 4 model edges that has no common model point and contains an edge with r=0 (so a common
     point would have to be a model point), or consists of var edges whose rest overlaps are all forced 0:
     union upper bound >= 61, where union bound = |union & model| + sum r - (Hunter tree of ro) for every tree.
  NK: for listed 5-pairs (X,Y): Z,Z' (not X,Y) with |Z&N|=|Z'&N|=1 and Z&Z'&N empty => |Z&Z'| >= 6.
  witness facts used as definitions only (WA&({y}uA_y)={p}); everything else (R.3 etc.) is derived by L.
"""
import sys, itertools, time, json
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model

M = list(range(5)); A = list(range(5, 21)); C = list(range(21, 37))
O = {y: list(range(37 + 12 * y, 49 + 12 * y)) for y in range(5)}
NPT = 97
import os
NKSLIM = os.environ.get('NKSLIM','0')=='1'

class Model:
    def __init__(self):
        self.m = cp_model.CpModel(); self.E = {}; self.rest = {}; self.cache = {}
    def const_edge(self, name, pts):
        s = set(pts); self.E[name] = [1 if p in s else 0 for p in range(NPT)]; self.rest[name] = 0
    def var_edge(self, name, fixed=None, rest_max=21):
        fixed = fixed or {}
        self.E[name] = [fixed[p] if p in fixed else self.m.NewBoolVar(f'{name}_{p}') for p in range(NPT)]
        r = self.m.NewIntVar(0, rest_max, f'r_{name}'); self.rest[name] = r
        self.m.Add(sum(self.E[name]) + r == 21)
    def AND(self, lits):
        lits = [l for l in lits if l is not 1]
        if any(l is 0 for l in lits): return 0
        if not lits: return 1
        if len(lits) == 1: return lits[0]
        key = ('and',) + tuple(sorted(id(l) for l in lits))
        if key in self.cache: return self.cache[key]
        z = self.m.NewBoolVar('')
        self.m.AddBoolAnd(lits).OnlyEnforceIf(z); self.m.AddBoolOr([l.Not() for l in lits] + [z])
        self.cache[key] = z; return z
    def OR(self, lits):
        lits = [l for l in lits if l is not 0]
        if any(l is 1 for l in lits): return 1
        if not lits: return 0
        if len(lits) == 1: return lits[0]
        key = ('or',) + tuple(sorted(id(l) for l in lits))
        if key in self.cache: return self.cache[key]
        z = self.m.NewBoolVar('')
        self.m.AddBoolOr(lits).OnlyEnforceIf(z)
        for l in lits: self.m.AddImplication(l, z)
        self.cache[key] = z; return z
    def cnt(self, names, pts=range(NPT), mode='and'):
        f = self.AND if mode == 'and' else self.OR
        return sum(f([self.E[n][p] for n in names]) for p in pts)

def build(cls=(2, 4), wit=('A0', 'C0'), others_wit=(), nkpairs='auto', fam_max=4, extraJ=(), fixF=None, lazy=False, lazy_init=()):
    md = Model(); m = md.m
    md.const_edge('E1', M + A); md.const_edge('E2', M + C)
    # singles
    for y in range(5):
        fx = {}
        for p in M: fx[p] = 1 if p == y else 0
        for z in range(5):
            for p in O[z]: fx[p] = 1 if z == y else 0
        if y == 0:
            for i, p in enumerate(A): fx[p] = 1 if i < 4 else 0
            for i, p in enumerate(C): fx[p] = 1 if i < 4 else 0
        if fixF and y in fixF:
            aa, cc = fixF[y]
            for i, p in enumerate(A): fx[p] = 1 if i in aa else 0
            for i, p in enumerate(C): fx[p] = 1 if i in cc else 0
        md.var_edge(f'F{y}', fx, rest_max=0)
        m.Add(sum(md.E[f'F{y}'][p] for p in A) == 4); m.Add(sum(md.E[f'F{y}'][p] for p in C) == 4)
    # class of (F0,F1)
    a, c = cls
    m.Add(md.cnt(['F0', 'F1'], A) == a); m.Add(md.cnt(['F0', 'F1'], C) == c)
    W = []
    def add_wit(y, side):
        Fy = f'F{y}'
        part = A if side == 'A' else C
        for p in part:
            # one witness per point of the part; existence is conditional on p in part_y -> use only y=0 (fixed parts)
            pass
    for w in wit + tuple(others_wit):
        side, y = w[0], int(w[1:])
        part = A if side == 'A' else C
        if y == 0: pts = part[:4]
        elif fixF and y in fixF: pts = [part[i] for i in (fixF[y][0] if side == 'A' else fixF[y][1])]
        else: raise ValueError('witnesses of a variable single need fixF')
        for p in pts:
            nm = f'W{side}{y}_{p}'
            fx = {q: 0 for q in M if q == y}
            Fy_part = [q for q in part if md.E[f'F{y}'][q] is 1]
            for q in Fy_part: fx[q] = 1 if q == p else 0
            fx[y] = 0
            md.var_edge(nm, fx); W.append((nm, y, side, p))
    for B in extraJ:
        nm = 'J' + '_'.join(map(str, B)); md.var_edge(nm, {p: 0 for p in B}); W.append((nm, None, 'J', B))
    names = list(md.E)
    # rest overlaps
    ro = {}
    for x, y in itertools.combinations(names, 2):
        if md.rest[x] is 0 or md.rest[y] is 0: ro[x, y] = ro[y, x] = 0; continue
        v = m.NewIntVar(0, 21, ''); m.Add(v <= md.rest[x]); m.Add(v <= md.rest[y]); ro[x, y] = ro[y, x] = v
    inter = {}
    for x, y in itertools.combinations(names, 2):
        if x in ('E1', 'E2') and y in ('E1', 'E2'): inter[x, y] = inter[y, x] = 5; continue
        e = md.cnt([x, y]); inter[x, y] = inter[y, x] = e
        m.Add(e + ro[x, y] >= 5)
    # L on families
    nfam = 0
    md.names = names; md.ro = ro
    def add_family(S):
        if True:
            closed = [n for n in S if md.rest[n] is 0]
            if not closed: return 0
            if set(S) >= {'E1', 'E2'} and len(closed) == len(S): return 0
            com = [md.AND([md.E[n][p] for n in S]) for p in range(NPT)]
            com = [c for c in com if c is not 0]
            if any(c is 1 for c in com): return 0
            un = md.cnt(S, mode='or')
            varS = [n for n in S if md.rest[n] is not 0]
            rs = sum(md.rest[n] for n in varS)
            trees = [[]]
            if len(varS) == 2: trees = [[(varS[0], varS[1])]]
            elif len(varS) == 3:
                a_, b_, c_ = varS; trees = [[(a_, b_), (a_, c_)], [(a_, b_), (b_, c_)], [(a_, c_), (b_, c_)]]
            elif len(varS) == 4:
                trees = [[(varS[0], varS[i]) for i in (1, 2, 3)]]  # star trees (sound, not all trees)
                trees += [[(varS[i], varS[j]) for j in range(4) if j != i] for i in (1, 2, 3)]
            for t in trees:
                bound = un + rs - sum(ro[e] for e in t)
                if com: m.Add(bound >= 61).OnlyEnforceIf([cc.Not() for cc in com])
                else: m.Add(bound >= 61)
            return 1
    md.add_family = add_family
    if not lazy:
        for k in range(3, fam_max + 1):
            for S in itertools.combinations(names, k): nfam += add_family(S)
    else:
        for S in lazy_init: nfam += add_family(S)
    # NK on 5-pairs
    if nkpairs == 'auto':
        nkpairs = [('E1', 'E2')] + [('E1', f'F{y}') for y in range(5)] + [('E2', f'F{y}') for y in range(5)]
        if not NKSLIM:
          for (nm, y, side, p) in W:
            if side == 'A': nkpairs += [('E1', nm), (f'F{y}', nm)]
            if side == 'C': nkpairs += [('E2', nm), (f'F{y}', nm)]
    nnk = 0
    for (X, Y) in nkpairs:
        Npts = [md.AND([md.E[X][p], md.E[Y][p]]) for p in range(NPT)]
        if (X, Y) != ('E1', 'E2'): m.Add(sum(Npts) == 5)   # these are 5-pairs by R.3 / definition
        sing = {}
        for Z in names:
            if Z in (X, Y): continue
            zn = sum(md.AND([Npts[p], md.E[Z][p]]) for p in range(NPT) if Npts[p] is not 0)
            b = m.NewBoolVar(''); m.Add(zn == 1).OnlyEnforceIf(b); m.Add(zn != 1).OnlyEnforceIf(b.Not()); sing[Z] = b
        for Z, Z2 in itertools.combinations(sing, 2):
            zz = sum(md.AND([Npts[p], md.E[Z][p], md.E[Z2][p]]) for p in range(NPT) if Npts[p] is not 0)
            dis = m.NewBoolVar(''); m.Add(zz == 0).OnlyEnforceIf(dis); m.Add(zz >= 1).OnlyEnforceIf(dis.Not())
            m.Add(inter[Z, Z2] + ro[Z, Z2] >= 6).OnlyEnforceIf([sing[Z], sing[Z2], dis]); nnk += 1
    return md, W, nfam, nnk

def solve(tl=100, workers=2, verbose=True, **kw):
    t0 = time.time(); md, W, nfam, nnk = build(**kw)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(md.m)
    res = dict(status=s.StatusName(st), t=round(time.time() - t0, 1), nfam=nfam, nnk=nnk)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = {}
        for n, lits in md.E.items():
            if n in ('E1', 'E2'): continue
            pts = [p for p in range(NPT) if (lits[p] if isinstance(lits[p], int) else s.Value(lits[p]))]
            r = md.rest[n]; r = r if isinstance(r, int) else s.Value(r)
            sol[n] = dict(pts=pts, M=[p for p in pts if p < 5], A=[p - 5 for p in pts if 5 <= p < 21],
                          C=[p - 21 for p in pts if 21 <= p < 37],
                          O={y: len([p for p in pts if p in O[y]]) for y in range(5)}, rest=r)
        res['sol'] = sol
    return res

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(); ap.add_argument('--cls', default='2,4'); ap.add_argument('--wit', default='A0,C0')
    ap.add_argument('--tl', type=float, default=100); ap.add_argument('--fam', type=int, default=4)
    a = ap.parse_args()
    cls = tuple(map(int, a.cls.split(','))); wit = tuple(x for x in a.wit.split(',') if x)
    aa, cc = cls
    fixF = {1: (list(range(aa)) + list(range(4, 8 - aa)), list(range(cc)) + list(range(4, 8 - cc)))}
    r = solve(tl=a.tl, cls=cls, wit=wit, fam_max=a.fam, fixF=fixF)
    print(json.dumps({k: v for k, v in r.items() if k != 'sol'}), flush=True)
    if 'sol' in r:
        for n, d in r['sol'].items(): print(n, d)
