r"""Wave 10: SOUND and EXACT encoding of outside points (Case N, r = 21).

Points: the 61 named points of the base B0..B3 (all of B0u..uB3), plus K POOL points u0..u{K-1} (outside the base),
plus implicit PRIVATE points: a new edge F has 21 - |F & (named u pool)| private points, each lying in no other model
edge.  So a model solution IS a literal partial hypergraph (base + new edges), and every union size is exact:
    |cup S| = 21|S| - sum_a (mult_S(a) - 1)^+      (sum over named and pool points; privates have mult 1).

SOUNDNESS (why UNSAT is a proof).  Let G be a counterexample containing the base, and let the model edges be edges of G
(possibly coinciding; each model edge is a "slot").  Let Sh = {u outside the base : u lies in >= 2 slots}.
 Lemma KB: |Sh| <= floor( sum_slots (21 - nu_s) / 2 ), nu_s = proved lower bound on |F_s & base|
   (nu = 9 for a single of a base 5-pair by R.3, nu = 5 for any other edge by Lemma A).  Proof: each u in Sh is counted
   >= 2 times in sum_s |F_s \ base| <= sum_s (21 - nu_s).
 Map Sh injectively into the pool (K >= bound), every other outside point of a slot is private.  Every clause below is
 either the definition of an auxiliary variable (satisfied when aux = its intended meaning) or an INSTANCE of a proved
 statement about G evaluated on these slots:
   E21, AV (each slot avoids its 4-set: tau >= 5), A (Lemma A), L (property L on the subfamily; exact union),
   R1 (a slot avoiding N\{y} at a base 5-pair contains y), R3 (singles of any 5-pair meet both sides in exactly 5),
   SA (Lemma S(a)/R.3: cross-type singles of a 5-pair have disjoint parts outside X u Y), D1 (Section 6.0),
   W7 (Theorem W7-I: cross-type singles of a 5-pair meet in >= 2 points on each side), TT (W7-1 + W7-I),
   NK (N-noK4 hypothesis: cross-type singles of a 5-pair meet in >= 6 points; only for branch nok4),
   POOL ("pool column used by 0 or >= 2 slots": WLOG by the definition of Sh),
   SB  (lex-leader on pool columns and on columns of interchangeable named points: all constraints are invariant
        under permuting these columns, so some solution in each orbit has sorted columns).
Lazy loop: solve -> decode literal hypergraph -> check L on EVERY subfamily (DFS) and R3/SA/D1/W7/NK/TT at EVERY 5-pair
-> add violated instances -> repeat.  'violation-free SAT' = explicit configuration satisfying all of the above literally.

usage: python3 w10x_exact.py BRANCH TAG [K=auto] [tlim=1000] [maxadd=300] [solvelim=900]
  BRANCH: k4:3211 | nok4:2,4 ; edges = first 24 edges of w9_cpt.json (k4) / w9_cn24.json (nok4) unless nedges=..
"""
import sys, os, itertools, json, time, threading
sys.path.append("work/e616/pylib")
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Cadical153
from w9lazy import base_k4, base_nok4

class Exact:
    def __init__(s, names, B, edges, K, nk, clfile=None, solver=True):
        s.nn = len(names); s.K = K
        s.names = list(names) + [f'u{i}' for i in range(K)]
        s.n = s.nn + K; s.B = B; s.nb = len(B); s.nk = nk
        s.top = 1; s.ncl = 0; s.tags = {}
        s.clf = open(clfile, 'w') if clfile else None
        s.solver = Cadical153() if solver else None
        s.T = s.newv(); s.add([s.T], 'def'); s.F = -s.T
        s.cache = {}; s.inst = []; s.instset = set()
        s.edges = []
        for e in edges:
            x = [s.newv() for _ in range(s.n)]
            s.edges.append(dict(avoid=sorted(e['avoid']), label=e['label'], x=x, groups=[]))
        s.base_eager()
    # ------------------------------------------------------------------ low level
    def newv(s):
        s.top += 1; return s.top
    def add(s, c, tag):
        if s.T in c: return
        c = [l for l in c if l != s.F]
        s.ncl += 1; t = tag.split(':')[0]; s.tags[t] = s.tags.get(t, 0) + 1
        if s.clf: s.clf.write(' '.join(map(str, c)) + ' 0\n')
        if s.solver is not None: s.solver.add_clause(c)
    def neg(s, l):
        return s.F if l == s.T else (s.T if l == s.F else -l)
    def AND(s, a, b):
        if a == s.F or b == s.F: return s.F
        if a == s.T: return b
        if b == s.T: return a
        if a == b: return a
        if a == -b: return s.F
        k = ('and', min(a, b), max(a, b))
        if k in s.cache: return s.cache[k]
        z = s.newv(); s.add([-z, a], 'def'); s.add([-z, b], 'def'); s.add([z, -a, -b], 'def')
        s.cache[k] = z; return z
    def ANDs(s, ls):
        r = s.T
        for l in ls: r = s.AND(r, l)
        return r
    def OR(s, a, b): return s.neg(s.AND(s.neg(a), s.neg(b)))
    def count(s, lits, cap, mode='both'):
        """unary counter o[k-1] for k = 1..cap.  mode 'up': sum>=k -> o_k ; 'down': o_k -> sum>=k ; 'both'."""
        lits = [l for l in lits if l != s.F]
        nt = sum(1 for l in lits if l == s.T); lits = sorted(l for l in lits if l != s.T)
        Kc = max(0, cap - nt)
        key = ('cnt', tuple(lits), Kc, mode)
        if key in s.cache: return [s.T] * min(nt, cap) + s.cache[key]
        def tot(ls):
            if len(ls) == 1: return [ls[0]]
            h = len(ls) // 2; A = tot(ls[:h]); Bv = tot(ls[h:])
            m = min(len(A) + len(Bv), Kc)
            O = [s.newv() for _ in range(m)]
            for i in range(len(A) + 1):
                for j in range(len(Bv) + 1):
                    if mode in ('up', 'both') and i + j >= 1 and m:
                        c = [O[min(i + j, m) - 1]]
                        if i: c.append(-A[i - 1])
                        if j: c.append(-Bv[j - 1])
                        s.add(c, 'def')
                    if mode in ('down', 'both') and i + j < m:
                        c = [-O[i + j]]
                        if i < len(A): c.append(A[i])
                        if j < len(Bv): c.append(Bv[j])
                        s.add(c, 'def')
            return O
        O = tot(lits)[:Kc] if (lits and Kc > 0) else []
        s.cache[key] = O
        return ([s.T] * nt + O)[:cap]
    def ge(s, o, k):
        if k <= 0: return s.T
        if k > len(o): return s.F
        return o[k - 1]
    def bits(s, p):
        if p < 0:
            k = ('base', p)
            if k not in s.cache: s.cache[k] = [s.T if a in s.B[-1 - p] else s.F for a in range(s.n)]
            return s.cache[k]
        return s.edges[p]['x']
    # ------------------------------------------------------------------ eager part
    def base_eager(s):
        B, nb, nn = s.B, s.nb, s.nn
        pool = range(nn, s.n)
        # base 5-pairs and groups
        s.bpairs = [(i, j) for i, j in itertools.combinations(range(nb), 2) if len(B[i] & B[j]) == 5]
        for p, e in enumerate(s.edges):
            for (i, j) in s.bpairs:
                N = B[i] & B[j]; rest = N - set(e['avoid'])
                if len(rest) == 1: e['groups'].append((i, j, next(iter(rest))))
        for p, e in enumerate(s.edges):
            x = e['x']
            for a in e['avoid']: s.add([-x[a]], 'AV')
            s.add([-s.ge(s.count(x, 22, 'up'), 22)], 'E21')
            for k in range(nb): s.add([s.ge(s.count([x[a] for a in sorted(B[k])], 5, 'down'), 5)], 'A')
            for r in range(2, nb + 1):          # L on S u {F}, S base
                for S in itertools.combinations(range(nb), r):
                    I = frozenset.intersection(*[B[k] for k in S]); U = frozenset.union(*[B[k] for k in S])
                    b = len(U) - 40
                    if b >= 21: continue
                    o = s.count([x[a] for a in sorted(U)], b + 1, 'up')
                    s.add([x[a] for a in sorted(I)] + [-s.ge(o, b + 1)], 'L')
            for (i, j) in s.bpairs:             # D1 at base 5-pairs
                N = B[i] & B[j]
                o = s.count([x[a] for a in sorted(B[i] | B[j])], 10, 'up')
                for a in N: s.add([x[a], -s.ge(o, 10)], 'D1')
            for (i, j, y) in e['groups']:       # R1 + R3 at base 5-pairs
                s.add([x[y]], 'R1')
                for k in (i, j): s.add([-s.ge(s.count([x[a] for a in sorted(B[k])], 6, 'up'), 6)], 'R3')
        # S(a) at base 5-pairs, eager: cross-type singles have disjoint parts outside B_i u B_j
        for p, q in itertools.combinations(range(len(s.edges)), 2):
            for (i, j, y) in s.edges[p]['groups']:
                for (i2, j2, y2) in s.edges[q]['groups']:
                    if (i, j) == (i2, j2) and y != y2:
                        for a in range(s.n):
                            if a not in B[i] and a not in B[j]:
                                s.add([-s.edges[p]['x'][a], -s.edges[q]['x'][a]], 'SA')
        # Lemma A for every pair of new edges (exact: privates are never shared)
        for p, q in itertools.combinations(range(len(s.edges)), 2):
            X, Y = s.bits(p), s.bits(q)
            o = s.count([s.AND(X[a], Y[a]) for a in range(s.n)], 5, 'down'); s.add([s.ge(o, 5)], 'A')
            for k in range(nb):    # F1 with one base edge (= L on {B_k,F,G} given Lemma A)
                s.add([s.AND(X[a], Y[a]) for a in sorted(B[k])], 'L')
        # POOL: a pool column is used by 0 or >= 2 slots
        m = len(s.edges)
        for u in pool:
            for p in range(m):
                s.add([-s.edges[p]['x'][u]] + [s.edges[q]['x'][u] for q in range(m) if q != p], 'POOL')
        # SB: lex-leader on interchangeable columns (pool; named points with identical base signature, in no avoid set)
        used = set(a for e in s.edges for a in e['avoid'])
        classes = {}
        for a in range(nn):
            if a in used: continue
            sig = tuple(k for k in range(nb) if a in B[k])
            classes.setdefault(sig, []).append(a)
        s.symclasses = [c for c in classes.values() if len(c) > 1] + ([list(pool)] if s.K > 1 else [])
        if not os.environ.get('W10X_NOSB'):     # control switch: build without symmetry breaking
            for cl in s.symclasses:
                for a, c in zip(cl, cl[1:]): s.lex_ge(a, c)
    def eager2(s):
        """eager lemma instances at the KNOWN 5-pairs: every base 5-pair (W7/NK, SA for all pairs of edges) and every
        second-generation pair (B_i, F) with F a single of a base pair through B_i (R3, D1 for every third edge)."""
        nb = s.nb; allE = list(range(-nb, 0)) + list(range(len(s.edges)))
        cnt = 0
        for (i, j) in s.bpairs:
            for z1, z2 in itertools.combinations(allE, 2):
                if z1 < 0 and z2 < 0: continue
                if -1 - i in (z1, z2) or -1 - j in (z1, z2): continue
                cnt += s.add_inst(['W7', -1 - i, -1 - j, z1, z2]) + s.add_inst(['SA', -1 - i, -1 - j, z1, z2])
        for p, e in enumerate(s.edges):
            for (i, j, y) in e['groups']:
                for X in (i, j):
                    for z in allE:
                        if z in (p, -1 - X): continue
                        cnt += s.add_inst(['R3', -1 - X, p, z]) + s.add_inst(['D1', -1 - X, p, z])
        return cnt
    def lex_ge(s, a, c):
        """column a >=lex column c (vectors over the new edges, edge 0 most significant)."""
        eq = s.T
        for e in s.edges:
            A, C = e['x'][a], e['x'][c]
            s.add([s.neg(eq), A, -C], 'SB')
            ne = s.newv()          # ne <-> eq & (A == C)
            s.add([-ne, A, -C], 'SB'); s.add([-ne, -A, C], 'SB')
            if eq != s.T: s.add([-ne, eq], 'SB')
            s.add([ne, s.neg(eq), A, C], 'SB'); s.add([ne, s.neg(eq), -A, -C], 'SB')
            eq = ne
    # ------------------------------------------------------------------ lazy instances
    def add_inst(s, ins):
        key = json.dumps(ins)
        if key in s.instset: return False
        s.instset.add(key); s.inst.append(ins); s.encode(ins); return True
    def pair5_x(s, X, Y):
        """escape literals for 'X & Y has exactly 5 points' plus the list N of intersection literals."""
        N = [s.AND(X[a], Y[a]) for a in range(s.n)]
        o = s.count(N, 6, 'both')
        return [s.neg(s.ge(o, 5)), s.ge(o, 6)], N
    def single_x(s, Z, N):
        o = s.count([s.AND(Z[a], N[a]) for a in range(s.n)], 2, 'both')
        return [s.neg(s.ge(o, 1)), s.ge(o, 2)]
    # shared counters on pair / triple intersections (exact both ways up to their caps)
    PC, TC = 11, 6
    def pa(s, p, q):
        k = ('pa',) + tuple(sorted((p, q)))
        if k not in s.cache:
            X, Y = s.bits(p), s.bits(q); s.cache[k] = [s.AND(X[a], Y[a]) for a in range(s.n)]
        return s.cache[k]
    def ta(s, p, q, r):
        p, q, r = sorted((p, q, r))
        k = ('ta', p, q, r)
        if k not in s.cache:
            Z = s.bits(r); s.cache[k] = [s.AND(l, Z[a]) for a, l in enumerate(s.pa(p, q))]
        return s.cache[k]
    def qa(s, p, q, r, t):
        p, q, r, t = sorted((p, q, r, t))
        W = s.bits(t); return [s.AND(l, W[a]) for a, l in enumerate(s.ta(p, q, r))]
    def pc(s, p, q): return s.count(s.pa(p, q), s.PC, 'both')
    def tc(s, p, q, r): return s.count(s.ta(p, q, r), s.TC, 'both')
    def gep(s, o, k):
        """positive-use literal for 'value >= k' from a capped counter: weakened to 'value >= cap' if k > cap (sound)."""
        if k <= 0: return s.T
        return o[min(k, len(o)) - 1] if o else s.F
    def pre5(s, p, q):
        o = s.pc(p, q); return [s.neg(s.ge(o, 5)), s.ge(o, 6)]
    def single(s, p, q, z):
        o = s.tc(p, q, z); return [s.neg(s.ge(o, 1)), s.ge(o, 2)]
    def encode(s, ins):
        kind = ins[0]
        if kind[0] == 'X': return s.encode_x([kind[1:]] + ins[1:])
        if kind == 'L':
            fam = ins[1]; m = len(fam)
            if m == 2: return
            if m == 3: s.add(s.ta(*fam), 'L'); return
            if m > 4: return s.encode_x(ins)
            guard = s.qa(*fam)
            lits = []; esc = []
            for p, q in itertools.combinations(fam, 2): lits += s.pc(p, q)
            for tr in itertools.combinations(fam, 3):
                o = s.tc(*tr); lits += [s.neg(l) for l in o]; esc.append(s.ge(o, s.TC))
            bound = 23 + 4 * s.TC
            o = s.count(lits, bound + 1, 'up')
            if len(o) > bound: s.add(guard + esc + [-s.ge(o, bound + 1)], 'L')
        elif kind == 'R3':
            p, q, z = ins[1:4]; pre = s.pre5(p, q) + s.single(p, q, z)
            for w in (p, q): s.add(pre + [s.neg(s.ge(s.pc(z, w), 6))], 'R3')
        elif kind == 'D1':
            p, q, l = ins[1:4]; pre = s.pre5(p, q)
            oX, oY, t = s.pc(l, p), s.pc(l, q), s.tc(l, p, q)
            for i in range(5, s.PC + 1):
                for j in range(5, s.PC + 1):
                    s.add(pre + [s.neg(s.ge(oX, i)), s.neg(s.ge(oY, j)), s.gep(t, min(i + j - 9, 5))], 'D1')
        elif kind in ('SA', 'W7'):
            p, q, z1, z2 = ins[1:5]
            pre = s.pre5(p, q) + s.single(p, q, z1) + s.single(p, q, z2) + s.qa(p, q, z1, z2)
            tX, tY = s.tc(z1, z2, p), s.tc(z1, z2, q)
            if kind == 'W7':
                s.add(pre + [s.ge(tX, 2)], 'W7'); s.add(pre + [s.ge(tY, 2)], 'W7')
                if s.nk: s.add(pre + [s.ge(s.pc(z1, z2), 6)], 'NK')
            else:
                c = s.newv(); s.add(pre + [c], 'SA'); oP = s.pc(z1, z2)
                for i in range(1, s.PC + 1):
                    for a in range(0, i + 1):
                        s.add([-c, s.neg(s.ge(oP, i)), s.gep(tX, a + 1), s.gep(tY, i - a)], 'SA')
        elif kind == 'N24':   # Wave 11: class (2,4)/(4,2) is impossible in N-noK4 (Wave 10 X.5 certificate); exact counters
            p, q, z1, z2 = ins[1:5]
            pre = s.pre5(p, q) + s.single(p, q, z1) + s.single(p, q, z2) + s.qa(p, q, z1, z2)
            tX, tY = s.tc(z1, z2, p), s.tc(z1, z2, q)
            for (u, w) in ((tX, tY), (tY, tX)):
                s.add(pre + [s.neg(s.ge(u, 2)), s.ge(u, 3), s.neg(s.ge(w, 4)), s.ge(w, 5)], 'N24')
        elif kind == 'TT':
            x, ys = ins[1], ins[2]; pre = []
            for y in ys: pre += s.pre5(x, y)
            for y1, y2 in itertools.combinations(ys, 2): pre += s.single(y1, y2, x)
            s.add(pre + s.qa(x, *ys), 'TT')
        else:
            raise ValueError(kind)
    def encode_x(s, ins):
        """per-point exact encodings (escalation when the counter form was not tight enough)."""
        kind = ins[0]
        if kind == 'L':
            fam = ins[1]; bb = [s.bits(p) for p in fam]; m = len(fam)
            if m == 2: return
            com = [s.ANDs([b[a] for b in bb]) for a in range(s.n)]
            if m == 3: s.add(com, 'L'); return
            slack = 21 * m - 61
            exc = []
            for a in range(s.n):
                ls = [b[a] for b in bb if b[a] != s.F]
                if len(ls) < 2: continue
                exc += s.count(ls, m, 'up')[1:]
            o = s.count(exc, slack + 1, 'up')
            s.add(com + [-s.ge(o, slack + 1)] if len(o) > slack else com + [s.T], 'L')
        elif kind in ('R3', 'SA', 'D1', 'W7'):
            p, q = ins[1], ins[2]; X, Y = s.bits(p), s.bits(q)
            pre, N = s.pair5_x(X, Y)
            if kind == 'R3':
                Z = s.bits(ins[3]); pre = pre + s.single_x(Z, N)
                for W in (X, Y):
                    o = s.count([s.AND(Z[a], W[a]) for a in range(s.n)], 6, 'up')
                    s.add(pre + [-s.ge(o, 6)], 'R3')
            elif kind == 'SA':
                Z1, Z2 = s.bits(ins[3]), s.bits(ins[4])
                pre = pre + s.single_x(Z1, N) + s.single_x(Z2, N) + [s.ANDs([Z1[a], Z2[a], N[a]]) for a in range(s.n)]
                c = s.newv(); s.add(pre + [c], 'SA')
                for a in range(s.n):
                    if X[a] == s.T or Y[a] == s.T: continue
                    s.add([-c, s.neg(Z1[a]), s.neg(Z2[a]), X[a], Y[a]], 'SA')
            elif kind == 'D1':
                Lb = s.bits(ins[3])
                o = s.count([s.AND(N[a], Lb[a]) for a in range(s.n)], 5, 'both')
                pre = pre + [s.ge(o, 5)]
                o2 = s.count([s.AND(Lb[a], s.OR(X[a], Y[a])) for a in range(s.n)], 10, 'up')
                s.add(pre + [-s.ge(o2, 10)], 'D1')
            else:   # W7 (+NK)
                Z1, Z2 = s.bits(ins[3]), s.bits(ins[4])
                pre = pre + s.single_x(Z1, N) + s.single_x(Z2, N) + [s.ANDs([Z1[a], Z2[a], N[a]]) for a in range(s.n)]
                ab = [s.AND(Z1[a], Z2[a]) for a in range(s.n)]
                for (P, Q) in ((X, Y), (Y, X)):
                    o = s.count([s.AND(ab[a], s.AND(P[a], s.neg(Q[a]))) for a in range(s.n)], 2, 'down')
                    s.add(pre + [s.ge(o, 2)], 'W7')
                if s.nk:
                    o = s.count(ab, 6, 'down'); s.add(pre + [s.ge(o, 6)], 'NK')
        elif kind == 'TT':
            X = s.bits(ins[1]); ys = [s.bits(p) for p in ins[2]]
            pre = []
            for b in ys:
                o = s.count([s.AND(b[a], X[a]) for a in range(s.n)], 6, 'both'); pre += [s.neg(s.ge(o, 5)), s.ge(o, 6)]
            for b1, b2 in itertools.combinations(ys, 2):
                o = s.count([s.ANDs([b1[a], b2[a], X[a]]) for a in range(s.n)], 2, 'both'); pre += [s.neg(s.ge(o, 1)), s.ge(o, 2)]
            com = [s.ANDs([ys[0][a], ys[1][a], ys[2][a], X[a]]) for a in range(s.n)]
            s.add(pre + com, 'TT')
        else:
            raise ValueError(kind)
    # ------------------------------------------------------------------ solve / decode / check
    def solve(s, lim=None):
        r = s.solver.solve()   # time limit is external (timeout + per-iteration checkpoint)
        if r is None: return 'TIMEOUT'
        if not r: return None
        m = set(l for l in s.solver.get_model() if l > 0)
        return [frozenset(a for a in range(s.n) if e['x'][a] in m) for e in s.edges]

def literal(md, sol):
    """explicit hypergraph: base + new edges; private points named ('p', edge, i)."""
    E = [frozenset(b) for b in md.B]
    for p, S in enumerate(sol):
        E.append(frozenset(S) | frozenset(('p', p, i) for i in range(21 - len(S))))
    return E

def check(md, sol, limit=600):
    E = literal(md, sol); nb = md.nb; n = len(E)
    idx = lambda k: -1 - k if k < nb else k - nb
    out = []
    assert all(len(x) == 21 for x in E), [len(x) for x in E]
    for i, j in itertools.combinations(range(n), 2):
        if len(E[i] & E[j]) < 5: out.append(['A?', idx(i), idx(j)])
    # L on every subfamily (union <= 60 and empty intersection), at least one new edge
    bad = []
    def dfs(start, U, I, fam):
        if len(bad) > limit: return
        if len(fam) >= 2 and not I and any(k >= nb for k in fam): bad.append(list(fam)); return
        for k in range(start, n):
            U2 = U | E[k]
            if len(U2) > 60: continue
            dfs(k + 1, U2, (I & E[k]) if fam else E[k], fam + [k])
    dfs(0, frozenset(), frozenset(), [])
    bad.sort(key=len)
    out += [['L', [idx(k) for k in f]] for f in bad]
    # 5-pairs
    for i, j in itertools.combinations(range(n), 2):
        N = E[i] & E[j]
        if len(N) != 5: continue
        U = E[i] | E[j]
        sing = {}
        for k in range(n):
            if k in (i, j): continue
            t = E[k] & N
            if len(t) == 1: sing.setdefault(next(iter(t)), []).append(k)
            if not (N <= E[k]) and len(E[k] & U) > 9 and not (k < nb and i < nb and j < nb):
                out.append(['D1', idx(i), idx(j), idx(k)])
        for t, ks in sing.items():
            for k in ks:
                if (len(E[k] & E[i]) != 5 or len(E[k] & E[j]) != 5) and not all(z < nb for z in (i, j, k)):
                    out.append(['R3', idx(i), idx(j), idx(k)])
        for t1, t2 in itertools.combinations(sing, 2):
            for a in sing[t1]:
                for b in sing[t2]:
                    if all(z < nb for z in (i, j, a, b)): continue
                    AB = E[a] & E[b]
                    if AB - U: out.append(['SA', idx(i), idx(j), idx(a), idx(b)])
                    if len(AB & (E[i] - E[j])) < 2 or len(AB & (E[j] - E[i])) < 2 or (md.nk and len(AB) < 6):
                        out.append(['W7', idx(i), idx(j), idx(a), idx(b)])
                    if getattr(md, 'no24', False) and not (AB - U) and sorted((len(AB & E[i]), len(AB & E[j]))) == [2, 4] and not (AB & N):
                        out.append(['N24', idx(i), idx(j), idx(a), idx(b)])
    # TT on every edge
    for x in range(n):
        cand = [k for k in range(n) if k != x and len(E[k] & E[x]) == 5]
        tr = {k: E[k] & E[x] for k in cand}
        for a, b, c in itertools.combinations(cand, 3):
            if all(z < nb for z in (x, a, b, c)): continue
            if len(tr[a] & tr[b]) == 1 and len(tr[a] & tr[c]) == 1 and len(tr[b] & tr[c]) == 1 and not (tr[a] & tr[b] & tr[c]):
                out.append(['TT', idx(x), [idx(a), idx(b), idx(c)]])
    return out

def setup(br, opt):
    if br.startswith('k4:'): names, B = base_k4(br[3:]); nk = False; src = 'w9_cpt.json'
    else: a, c = map(int, br[5:].split(',')); names, B = base_nok4(a, c); nk = True; src = 'w9_cn24.json'
    ne = int(opt.get('nedges', 24))
    here = os.path.dirname(os.path.abspath(__file__))
    edges = json.load(open(os.path.join(here, opt.get('src', src))))['edges'][:ne]
    if opt.get('gen1auto'):   # all first-generation singles: every base 5-pair, every type not realised by a base edge
        edges = []
        for i, j in itertools.combinations(range(len(B)), 2):
            N = B[i] & B[j]
            if len(N) != 5: continue
            real = set(next(iter(B[k] & N)) for k in range(len(B)) if k not in (i, j) and len(B[k] & N) == 1)
            for y in sorted(N - real):
                edges.append(dict(avoid=sorted(N - {y}), gen=1, label=f'g1:(B{j},B{i}):{names[y]}'))
    if 'sel' in opt: edges = [edges[int(t)] for t in opt['sel'].split(',') if t not in ('', 'none')]  # W13: sel=none -> no first-gen singles
    if opt.get('extra'):      # Wave 11 (additive; absent -> unchanged): extra tau-edges 'lab@p1+p2+p3+p4;...' (named points)
        ix = {nm: i for i, nm in enumerate(names)}
        for tok in opt['extra'].split(';'):
            lab_, pts = tok.split('@')
            edges.append(dict(avoid=sorted(ix[t] for t in pts.split('+')), gen=2, label=lab_))
    # Lemma KB bound
    nbB = len(B); bp = [(i, j) for i, j in itertools.combinations(range(nbB), 2) if len(B[i] & B[j]) == 5]
    cap = 0
    for e in edges:
        single = any(len((B[i] & B[j]) - set(e['avoid'])) == 1 for i, j in bp)
        cap += 21 - (9 if single else 5)
    Kb = cap // 2
    K = Kb if opt.get('K', 'auto') == 'auto' else int(opt['K'])
    return names, B, nk, edges, K, Kb

if __name__ == '__main__':
    br, TAG = sys.argv[1], sys.argv[2]
    opt = dict(f.split('=', 1) for f in sys.argv[3:] if '=' in f)
    here = os.path.dirname(os.path.abspath(__file__))
    names, B, nk, edges, K, Kb = setup(br, opt)
    tlim = float(opt.get('tlim', 1000)); maxadd = int(opt.get('maxadd', 300)); slim = float(opt.get('solvelim', 900))
    print(f'branch {br} edges {len(edges)} K={K} (KB bound {Kb}; sound={K >= Kb and not opt.get("tame")}) opt={opt}', flush=True)
    t0 = time.time()
    md = Exact(names, B, edges, K, nk)
    if opt.get('eager2'): print('eager2 instances', md.eager2(), flush=True)
    if opt.get('tame'):   # CONSTRUCTIVE ONLY (not sound): no accidental 5-pairs among new edges / new-base
        for p_, q_ in itertools.combinations(range(len(md.edges)), 2): md.add([md.ge(md.pc(p_, q_), 6)], 'TAME')
        if opt['tame'] == '2':
            for p_, e in enumerate(md.edges):
                gb = set(k for (i, j, y) in e['groups'] for k in (i, j))
                for k in range(md.nb):
                    if k not in gb: md.add([md.ge(md.pc(p_, -1 - k), 6)], 'TAME')
    ck = os.path.join(here, f'w10x_{TAG}.json')
    if os.path.exists(ck):
        st = json.load(open(ck))
        for ins in st['inst']: md.add_inst(ins)
        print('restored', len(md.inst), 'instances', flush=True)
    print(f'built {time.time()-t0:.1f}s vars={md.top} clauses={md.ncl} tags={md.tags}', flush=True)
    def save(extra=None):
        d = dict(branch=br, K=K, Kb=Kb, opt=opt, inst=md.inst)
        if extra: d.update(extra)
        json.dump(d, open(ck + '.tmp', 'w')); os.replace(ck + '.tmp', ck)
    T0 = time.time()
    for it in range(100000):
        t1 = time.time(); r = md.solve(slim); ts = time.time() - t1
        if r == 'TIMEOUT':
            print(f'it {it}: solve TIMEOUT ({ts:.0f}s) inst={len(md.inst)} cl={md.ncl}', flush=True); save(); break
        if r is None:
            print(f'it {it}: UNSAT ({ts:.1f}s) inst={len(md.inst)} vars={md.top} clauses={md.ncl} sound={K >= Kb and not opt.get("tame")}', flush=True)
            save(dict(result='UNSAT')); open(os.path.join(here, f'w10x_{TAG}.UNSAT'), 'w').write('UNSAT\n'); break
        v = check(md, r)
        pri = {'A?': 0, 'R3': 1, 'SA': 1, 'W7': 2, 'TT': 2, 'D1': 3, 'L': 4}
        v.sort(key=lambda z: (pri[z[0]], len(z[1]) if z[0] == 'L' else 0))
        assert not any(z[0] == 'A?' for z in v)
        added = 0
        esc = 0
        byk = {}
        for z in v: byk.setdefault(z[0], []).append(z)
        rr = []; its = [iter(l) for l in byk.values()]
        while its:
            nxt = []
            for itr in its:
                z = next(itr, None)
                if z is not None: rr.append(z); nxt.append(itr)
            its = nxt
        v = rr
        for z in v:
            if added >= maxadd: break
            if json.dumps(z) in md.instset:
                z = ['X' + z[0]] + z[1:]; esc += 1
                if json.dumps(z) in md.instset: print('BUG: exact instance present but violated', z, flush=True); continue
            added += md.add_inst(z)
        kinds = {}
        for z in v: kinds[z[0]] = kinds.get(z[0], 0) + 1
        pu = sorted(set(a for S in r for a in S if a >= md.nn))
        print(f'it {it}: SAT ({ts:.1f}s) inst={len(md.inst)} cl={md.ncl} viol={len(v)} {kinds} added={added} esc={esc} pool_used={len(pu)}', flush=True)
        if added == 0:
            if v: print('WARNING: violations not encodable/duplicate', v[:5], flush=True)
            E = literal(md, r)
            json.dump(dict(branch=br, names=md.names, labels=[f'B{i}' for i in range(md.nb)] + [e['label'] for e in md.edges],
                           edges=[sorted(str(a) if isinstance(a, tuple) else md.names[a] for a in X) for X in E]),
                      open(os.path.join(here, f'w10x_{TAG}_real.json'), 'w'))
            print('VIOLATION-FREE: literal configuration written', flush=True); save(dict(result='REALIZED')); break
        save()
        if time.time() - T0 > tlim: print('time limit; checkpointed', flush=True); break
