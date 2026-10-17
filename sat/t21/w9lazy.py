r"""Wave 9: lazy CEGAR on a sound U-mode point model, with SECOND-GENERATION singles.

Base: 4 edges B0..B3, every point of B0u..uB3 named (61 points).  New edges F: 0/1 vectors over the named points,
plus U-overlap variables yu[F,G][k] with EXACT meaning "|F&G&U| >= k" (k = 1..CAP), U = points outside the base.
Every clause is one instance of a proved lemma (tag in brackets), or a definitional clause of an auxiliary
counter/AND variable (tag 'def'; such clauses can always be satisfied by giving the aux variable its true value):
 eager, per new edge F:
  [E21] |F & named| <= 21.          [A] Lemma A: |F & B_k| >= 5.
  [L1:S] L on S u {F}, S a set of base edges: F & (cap S) = {}  =>  |F & (cup S)| <= |cup S| - 40
         (S = 2 base edges with 5-pair: R.1 transversality; S = 3: L3 / N.0(ii)).
  [D1] D1 at every base 5-pair.     [AV] F avoids its 4-set B (tau >= 5: such an edge exists).
 lazy (added when the current solution violates them):
  [LA] Lemma A for two new edges: |F&G&named| + |F&G&U| >= 5.
  [L2:S] L on S u {F,G}: F&G&(cap S) = {}  =>  |F&cupS| + |G&cupS| + |F&G \ cupS| <= |cupS| - 19.
  [F1t] F1 for three new edges: a common named point, or every pair has a common U-point.
  [TT:X] no trace triangle on a base edge X (W7-1 + W7-I): three other edges meeting X in exactly 5, whose traces
         pairwise meet in exactly 1 point, have a common point.  (= NT at every 5-pair (X,Y), A-side.)
  [NK]   (N-noK4 branch only, hypothesis NK): if X&Y = N exactly (5 named points; for two new edges also no common
         U-point) and Z, Z' are singles of (X,Y) of different types, then |Z&Z'| >= 6.
  [NTC]  NT C-side at a 5-pair (X,Y) with fully named X&Y = N and Y base (A-side is TT).
  [CAP]  if G_1..G_k have pairwise no common U-point, then sum_j |F&G_j&U| <= 21 - |F & named|.
CEGAR on edges: every 5-pair (X,Y) of the current solution whose intersection N is fully named, with
gen(X), gen(Y) <= GMAX-1, needs for every y in N an edge avoiding N\{y} (R.2).  If no edge of the model does that in the
current solution, a new generic edge with avoid-set N\{y} is added (gen = max(gen X, gen Y) + 1).  Base = gen 0,
first-generation singles = gen 1, SECOND-generation singles = gen 2.
"""
import sys, os, itertools, json, time
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'pylib'))
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Cadical153

CAP = 6
def flags_get(flags, k, d):
    for f in flags:
        if isinstance(f, str) and f.startswith(k + '='): return f.split('=', 1)[1]
    return d

def base_k4(pat):
    from w8k4 import base_named, PAT
    pts, _ = base_named(PAT[pat])
    names = [p[0] for p in pts]
    B = [frozenset(a for a in range(len(pts)) if i in pts[a][1]) for i in range(4)]
    return names, B

def base_nok4(a, c):
    names = ['v', 'w', 'm0', 'm1', 'm2']
    def add(pref, k):
        s = len(names); names.extend(f'{pref}{i}' for i in range(k)); return list(range(s, s + k))
    M = [0, 1, 2, 3, 4]
    al = add('al', a); ag = add('ag', 4 - a); ah = add('ah', 4 - a); a0 = add('a0', 16 - len(al) - len(ag) - len(ah))
    cl = add('cl', c); cg = add('cg', 4 - c); ch = add('ch', 4 - c); c0 = add('c0', 16 - len(cl) - len(cg) - len(ch))
    og = add('og', 12); oh = add('oh', 12)
    E1 = frozenset(M + al + ag + ah + a0); E2 = frozenset(M + cl + cg + ch + c0)
    G = frozenset([0] + al + ag + cl + cg + og); H = frozenset([1] + al + ah + cl + ch + oh)
    assert all(len(x) == 21 for x in (E1, E2, G, H)) and len(names) == 61
    return names, [E1, E2, G, H]

class Model:
    def __init__(s, names, B, nk=False, gmax=2, flags=()):
        s.names, s.B, s.nk, s.gmax = names, B, nk, gmax
        s.n = len(names); s.flags = set(flags)
        s.top = 1; s.ncl = 0; s.tagcount = {}
        s.clf = open(flags_get(flags, 'clfile', '/tmp/w9_clauses.txt'), 'w')
        s.T = s.newv(); s.add([s.T], 'def'); s.F = -s.T
        s.edges = []   # dict(label, avoid, gen, x)
        s.yu = {}; s.inst = []; s.instset = set()
        s.solver = Cadical153()
        s.cache = {}
    # ---------- low level
    def newv(s):
        s.top += 1; return s.top
    def add(s, c, tag):
        if s.T in c: return
        c = [l for l in c if l != s.F]
        s.ncl += 1; s.tagcount[tag.split(':')[0]] = s.tagcount.get(tag.split(':')[0], 0) + 1
        s.clf.write(tag + ' ' + ' '.join(map(str, c)) + '\n')
        if hasattr(s, 'solver'): s.solver.add_clause(c)
    def AND(s, a, b):
        if a == s.F or b == s.F: return s.F
        if a == s.T: return b
        if b == s.T: return a
        k = ('and', min(a, b), max(a, b))
        if k in s.cache: return s.cache[k]
        z = s.newv(); s.add([-z, a], 'def'); s.add([-z, b], 'def'); s.add([z, -a, -b], 'def')
        s.cache[k] = z; return z
    def count(s, lits, cap):
        """returns o with o[k-1] -> (sum >= k)?  We need both directions for soundness of uses:
        we use '-o[k-1]' as 'sum <= k-1' (needs sum>=k -> o[k-1]) and 'o[k-1]' as 'sum >= k' (needs o -> sum>=k).
        Full totalizer gives both."""
        lits = [l for l in lits if l != s.F]
        nt = sum(1 for l in lits if l == s.T); lits = [l for l in lits if l != s.T]
        K = max(0, cap - nt)
        def tot(ls):
            if len(ls) == 1: return [ls[0]]
            h = len(ls) // 2; A = tot(ls[:h]); Bv = tot(ls[h:])
            m = min(len(A) + len(Bv), K)
            O = [s.newv() for _ in range(m)]
            for i in range(len(A) + 1):
                for j in range(len(Bv) + 1):
                    if i + j >= 1:
                        c = [O[min(i + j, m) - 1]] if m else None
                        if c is not None:
                            if i: c.append(-A[i - 1])
                            if j: c.append(-Bv[j - 1])
                            s.add(c, 'def')
                    if i + j < m:
                        c = [-O[i + j]]
                        if i < len(A): c.append(A[i])
                        if j < len(Bv): c.append(Bv[j])
                        s.add(c, 'def')
            return O
        O = tot(lits)[:K] if (lits and K > 0) else []
        return [s.T] * nt + O
    def ge(s, o, k):
        if k <= 0: return s.T
        if k > len(o): return s.F
        return o[k - 1]
    # ---------- edges
    def bits(s, p):
        """p >= 0: new edge index; p < 0: base edge -1-p (constants)."""
        if p < 0: return [s.T if a in s.B[-1 - p] else s.F for a in range(s.n)]
        return s.edges[p]['x']
    def add_edge(s, avoid, gen, label):
        x = [s.newv() for _ in range(s.n)]
        idx = len(s.edges); s.edges.append(dict(label=label, avoid=sorted(avoid), gen=gen, x=x))
        for a in avoid: s.add([-x[a]], 'AV')
        s.add([-s.ge(s.count(x, 22), 22)], 'E21')
        for Bk in s.B:
            s.add([s.ge(s.count([x[a] for a in Bk], 5), 5)], 'A')
        nb = len(s.B)
        for r in range(2, nb + 1):
            for S in itertools.combinations(range(nb), r):
                I = frozenset.intersection(*[s.B[k] for k in S]); U = frozenset.union(*[s.B[k] for k in S])
                b = len(U) - 40
                if b >= 21: continue
                o = s.ucnt(idx, S)
                s.add([x[a] for a in sorted(I)] + [-s.ge(o, b + 1)], f'L1:{S}')
        for k, l in itertools.combinations(range(nb), 2):
            N = s.B[k] & s.B[l]
            if len(N) != 5: continue
            o = s.count([x[a] for a in sorted(s.B[k] | s.B[l])], 10)
            for a in N: s.add([x[a], -s.ge(o, 10)], 'D1')
        return idx
    def ucnt(s, p, S):
        k = ('u', p, tuple(S))
        if k not in s.cache:
            U = frozenset.union(*[s.B[j] for j in S]); X = s.bits(p)
            s.cache[k] = s.count([X[a] for a in sorted(U)], max(1, len(U) - 23))
        return s.cache[k]
    def sumbound(s, oa, ob, ov, bound, guard, tag):
        # oa + ob + ov <= bound unless a guard literal holds; oa, ob, ov unary (o[k-1] <-> sum >= k, exact up to len)
        for i in range(len(oa) + 1):
            for j in range(len(ob) + 1):
                lim = bound - i - j + 1
                if lim > len(ov): continue
                c = list(guard)
                if i: c.append(-s.ge(oa, i))
                if j: c.append(-s.ge(ob, j))
                if lim >= 1: c.append(-s.ge(ov, lim))
                s.add(c, tag)
    def Y(s, p, q):
        """U-overlap vars for two new edges (exact semantics |F&G&U| >= k)."""
        if p < 0 or q < 0: return [s.F] * CAP
        k = (min(p, q), max(p, q))
        if k not in s.yu:
            v = [s.newv() for _ in range(CAP)]
            for i in range(CAP - 1): s.add([-v[i + 1], v[i]], 'def')
            s.yu[k] = v
        return s.yu[k]
    # ---------- lazy instances
    def add_inst(s, ins):
        key = json.dumps(ins)
        if key in s.instset: return False
        s.instset.add(key); s.inst.append(ins); s.encode(ins); return True
    def encode(s, ins):
        kind = ins[0]
        if kind == 'LA':
            p, q = ins[1], ins[2]; X, Yb = s.bits(p), s.bits(q)
            o = s.count([s.AND(X[a], Yb[a]) for a in range(s.n)] + s.Y(p, q), 5)
            s.add([s.ge(o, 5)], 'LA')
        elif kind == 'L2':
            p, q, S = ins[1], ins[2], ins[3]; X, Yb = s.bits(p), s.bits(q)
            I = frozenset.intersection(*[s.B[k] for k in S]); U = frozenset.union(*[s.B[k] for k in S])
            bnd = len(U) - 19
            ov = s.count([s.AND(X[a], Yb[a]) for a in range(s.n) if a not in U] + s.Y(p, q), max(1, bnd - 9))
            guard = [s.AND(X[a], Yb[a]) for a in sorted(I)]
            if bnd < 10:   # Lemma A gives |X&B| >= 5 for every base B, so the bound is violated: F1-type clause
                s.add(guard, f'L2:{tuple(S)}')
            else:
                s.sumbound(s.ucnt(p, S), s.ucnt(q, S), ov, bnd, guard, f'L2:{tuple(S)}')
        elif kind == 'F1t':
            p, q, r = ins[1], ins[2], ins[3]; X, Yb, Z = s.bits(p), s.bits(q), s.bits(r)
            com = [s.AND(s.AND(X[a], Yb[a]), Z[a]) for a in range(s.n)]
            for (u, v) in ((p, q), (p, r), (q, r)): s.add(com + [s.Y(u, v)[0]], 'F1t')
        elif kind == 'TT':
            X = s.B[ins[1]]; ys = ins[2]
            bb = [s.bits(p) for p in ys]; Xl = sorted(X)
            pre = []
            for b in bb:
                o = s.count([b[a] for a in Xl], 6)
                pre += [-s.ge(o, 5), s.ge(o, 6)]
            for i, j in itertools.combinations(range(3), 2):
                o = s.count([s.AND(bb[i][a], bb[j][a]) for a in Xl], 2)
                pre += [-s.ge(o, 1), s.ge(o, 2)]
            com = [s.AND(s.AND(bb[0][a], bb[1][a]), bb[2][a]) for a in Xl]
            s.add(pre + com, f'TT:{ins[1]}')
        elif kind in ('NK', 'NTC'):
            # ins = (kind, X, Yi, Z, Z2, N) ; X&Y = N exactly
            _, p, q, z1, z2, N = ins
            X, Yb, A, Bv = s.bits(p), s.bits(q), s.bits(z1), s.bits(z2)
            pre = [-X[a] for a in N] + [-Yb[a] for a in N]
            pre += [s.AND(X[a], Yb[a]) for a in range(s.n) if a not in N]
            pre += [s.Y(p, q)[0]]
            # Z, Z2 singles of types z != z2 : |Z & N| = 1, |Z2&N| = 1, Z&Z2&N = {}
            for b in (A, Bv):
                o = s.count([b[a] for a in N], 2); pre += [-s.ge(o, 1), s.ge(o, 2)]
            pre += [s.AND(A[a], Bv[a]) for a in N]
            if kind == 'NK':
                o = s.count([s.AND(A[a], Bv[a]) for a in range(s.n)] + s.Y(z1, z2), 6)
                s.add(pre + [s.ge(o, 6)], 'NK')
            else:   # C-side of NT, Y base: |Z&Z2&(Y\N)| >= 2
                Yset = s.B[-1 - q]
                o = s.count([s.AND(A[a], Bv[a]) for a in sorted(Yset - set(N))], 2)
                s.add(pre + [s.ge(o, 2)], 'NTC')
        elif kind in ('NKg', 'NTCg'):
            # NKg: (kind, Xbase_index(neg), Ynew, z1, z2): X base, (X,Y) 5-pair, z1,z2 cross-type singles -> |Z1&Z2| >= 6
            # NTCg: (kind, P, Qbase(neg), z1, z2): (P,Q) 5-pair, cross-type singles -> |Z1&Z2&(Q\P)| >= 2  (W7-I, C-side)
            _, p, q, z1, z2 = ins
            if kind == 'NKg': Qset = sorted(s.B[-1 - p]); Yb = s.bits(q)
            else: Qset = sorted(s.B[-1 - q]); Yb = s.bits(p)
            A, Bv = s.bits(z1), s.bits(z2)
            o = s.count([Yb[a] for a in Qset], 6); pre = [-s.ge(o, 5), s.ge(o, 6)]
            for b in (A, Bv):
                o = s.count([s.AND(Yb[a], b[a]) for a in Qset], 2); pre += [-s.ge(o, 1), s.ge(o, 2)]
            pre += [s.AND(s.AND(A[a], Bv[a]), Yb[a]) for a in Qset]
            if kind == 'NKg':
                o = s.count([s.AND(A[a], Bv[a]) for a in range(s.n)] + s.Y(z1, z2), 6)
                s.add(pre + [s.ge(o, 6)], 'NK')
            else:
                o = s.count([s.AND(s.AND(A[a], Bv[a]), -Yb[a]) for a in Qset], 2)
                s.add(pre + [s.ge(o, 2)], 'NTC')
        elif kind == 'CAP':
            p, gs = ins[1], ins[2]; X = s.bits(p)
            pre = [s.Y(g, h)[0] for g, h in itertools.combinations(gs, 2)]
            lits = list(X) + [l for g in gs for l in s.Y(p, g)]
            o = s.count(lits, 22)
            s.add(pre + [-s.ge(o, 22)], 'CAP')
        else:
            raise ValueError(kind)
    # ---------- solving and checking
    def solve(s):
        r = s.solver.solve()
        if not r: return None
        m = set(l for l in s.solver.get_model() if l > 0)
        sol = [frozenset(a for a in range(s.n) if e['x'][a] in m) for e in s.edges]
        yu = {k: sum(1 for l in v if l in m) for k, v in s.yu.items()}
        return sol, yu
    def edgeset(s, sol, p): return s.B[-1 - p] if p < 0 else sol[p]

def find_violations(md, sol, yu, limit=400):
    """evaluate every lazy-instance type on the solution; return list of violated instances (not yet present)."""
    n_new = len(sol); B = md.B; nb = len(B)
    out = []
    def U(p, q): return yu.get((min(p, q), max(p, q)), 0)
    allE = list(range(-nb, 0)) + list(range(n_new))
    S_list = [S for r in range(2, nb) for S in itertools.combinations(range(nb), r)]
    for p, q in itertools.combinations(range(n_new), 2):
        X, Yb = sol[p], sol[q]
        inter = X & Yb
        if len(inter) + U(p, q) < 5: out.append(['LA', p, q])
        for S in [(k,) for k in range(nb)] + S_list:
            I = frozenset.intersection(*[B[k] for k in S]); Un = frozenset.union(*[B[k] for k in S])
            if inter & I: continue
            lhs = len(X & Un) + len(Yb & Un) + len(inter - Un) + U(p, q)
            if lhs > len(Un) - 19: out.append(['L2', p, q, list(S)])
        if len(out) > limit: return out
    for p, q, r in itertools.combinations(range(n_new), 3):
        if sol[p] & sol[q] & sol[r]: continue
        if U(p, q) and U(p, r) and U(q, r): continue
        out.append(['F1t', p, q, r])
        if len(out) > limit: return out
    # TT on base edges
    for i in range(nb):
        X = B[i]
        cand = [p for p in allE if p != -1 - i and len(md.edgeset(sol, p) & X) == 5]
        tr = {p: md.edgeset(sol, p) & X for p in cand}
        for a, b, c in itertools.combinations(cand, 3):
            if a < 0 and b < 0 and c < 0: continue
            if len(tr[a] & tr[b]) == 1 and len(tr[a] & tr[c]) == 1 and len(tr[b] & tr[c]) == 1 and not (tr[a] & tr[b] & tr[c]):
                out.append(['TT', i, [a, b, c]])
    # 5-pairs with fully named intersection
    for X_, Y_ in fivepairs(md, sol, yu):
        N = md.edgeset(sol, X_) & md.edgeset(sol, Y_)
        singles = {}
        for z in allE:
            if z in (X_, Y_): continue
            t = md.edgeset(sol, z) & N
            if len(t) == 1: singles.setdefault(next(iter(t)), []).append(z)
        types = list(singles)
        for t1, t2 in itertools.combinations(types, 2):
            for z1 in singles[t1]:
                for z2 in singles[t2]:
                    Z1, Z2 = md.edgeset(sol, z1), md.edgeset(sol, z2)
                    if md.nk:
                        tot = len(Z1 & Z2) + (U(z1, z2) if z1 >= 0 and z2 >= 0 else 0)
                        if tot < 6:
                            if X_ < 0 and Y_ >= 0: out.append(['NKg', X_, Y_, z1, z2])
                            elif Y_ < 0 and X_ >= 0: out.append(['NKg', Y_, X_, z1, z2])
                            else: out.append(['NK', X_, Y_, z1, z2, sorted(N)])
                    for (P_, Q_) in ((X_, Y_), (Y_, X_)):
                        if Q_ < 0:   # C-side wrt base Q_
                            if len(Z1 & Z2 & (B[-1 - Q_] - N)) < 2:
                                out.append(['NTCg', P_, Q_, z1, z2])
    # capacity
    for p in range(n_new):
        nbrs = sorted([q for q in range(n_new) if q != p and U(p, q) > 0], key=lambda q: -U(p, q))
        grp = []
        for q in nbrs:
            if all(U(q, g) == 0 for g in grp): grp.append(q)
        if len(sol[p]) + sum(U(p, g) for g in grp) > 21 and len(grp) >= 2:
            out.append(['CAP', p, grp])
    return out

def fivepairs(md, sol, yu):
    nb = len(md.B); allE = list(range(-nb, 0)) + list(range(len(sol)))
    res = []
    for X_, Y_ in itertools.combinations(allE, 2):
        if X_ >= 0 and Y_ >= 0 and yu.get((X_, Y_), 0) > 0: continue
        if len(md.edgeset(sol, X_) & md.edgeset(sol, Y_)) == 5: res.append((X_, Y_))
    return res

def gen_of(md, p): return 0 if p < 0 else md.edges[p]['gen']

def needed_edges(md, sol, yu):
    r"""4-sets N\{y} at 5-pairs (gen <= gmax-1 on both sides) that no model edge avoids."""
    nb = len(md.B); allE = list(range(-nb, 0)) + list(range(len(sol)))
    need = {}
    for X_, Y_ in fivepairs(md, sol, yu):
        g = max(gen_of(md, X_), gen_of(md, Y_)) + 1
        if g > md.gmax: continue
        if getattr(md, 'bonly', False) and X_ >= 0 and Y_ >= 0: continue
        N = md.edgeset(sol, X_) & md.edgeset(sol, Y_)
        for y in N:
            Bs = N - {y}
            if any(not (md.edgeset(sol, z) & Bs) for z in allE): continue
            key = tuple(sorted(Bs))
            if key not in need or need[key][0] > g: need[key] = (g, X_, Y_, y)
    return need
