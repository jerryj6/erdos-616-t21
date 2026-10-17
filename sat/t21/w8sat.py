r"""Wave 8 N-K4: pure-CNF point model (pysat/CaDiCaL, DRAT-capable).
Base: K4 P0..P3 (pairwise 5, empty 4-fold intersection), triple sizes from PAT.  ALL points of P0..P3 are named
(core points + private parts O_i).  Points outside P0u..uP3 ("U") are NOT modelled: every constraint below is a
TRUE consequence that stays true when U-points are deleted (U only ever helps an edge reach size 21 or adds
overlap that would make unions SMALLER, so dropping U-overlaps weakens nothing that we assert).
New edges F: singles S^{ij}_x (pair (i,j), type x in N_ij) selected by the caller.
 (S)   F & N_ij = {x}; |F&P_i| = |F&P_j| = 5 (R.3); |F&P_k| >= 5 (Lemma A); |F & named| <= 21.
 (F1)  F meets every N_kl; F,G,P_k have a common point (P_k is fully named).
 (D1)  N_kl not inside F  =>  |F & (P_k u P_l)| <= 9.
 (L3)  F & T_ijk = {}  =>  |F & (P_i u P_j u P_k)| <= 8 + t_ijk.
 (L4)  F & G & N_kl = {}  =>  |F&(PkuPl)| + |G&(PkuPl)| + |F&G&named \ (PkuPl)| <= 18.   [L on {P_k,P_l,F,G}]
 (L5)  F & G & T_ijk = {} =>  |F&B| + |G&B| + |F&G&named \ B| <= 29 + t,  B = P_iuP_juP_k. [L on 5 edges]
 (NT)  same-pair cross-type singles: |A&A'| >= 2, |C&C'| >= 2 (no triangle, Theorem W7-I).
 (TT)  optional: no trace triangle on a base edge (W7-1 + W7-I) among base+new edges.
 (SB)  optional symmetry breaking: columns of points inside each O_i are lex-sorted (O_i points are interchangeable).
"""
import sys, itertools, time, os, json
sys.path.append("work/e616/pylib")
from pysat.formula import IDPool, CNF
from pysat.solvers import Cadical153
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w8k4 import base_named, witnesses, PAT, base

class Enc:
    def __init__(s):
        s.pool = IDPool(); s.cl = []
        s.T, s.F = None, None
        t = s.new(); s.cl.append([t]); s.T = t; s.F = -t
    def new(s): return s.pool.id(('aux', len(s.pool.obj2id)))
    def AND(s, a, b):
        if a == s.F or b == s.F: return s.F
        if a == s.T: return b
        if b == s.T: return a
        z = s.new(); s.cl += [[-z, a], [-z, b], [z, -a, -b]]; return z
    def count(s, lits, cap=None):
        """unary totalizer, truncated at cap: returns o with o[k-1] <-> (sum >= k) for k = 1..min(len, cap)."""
        lits = [l for l in lits if l != s.F]
        nt = sum(1 for l in lits if l == s.T); lits = [l for l in lits if l != s.T]
        K = None if cap is None else max(0, cap - nt)
        def tot(ls):
            if len(ls) == 1: return [ls[0]]
            h = len(ls) // 2; A = tot(ls[:h]); B = tot(ls[h:])
            n = len(A) + len(B) if K is None else min(len(A) + len(B), K)
            O = [s.new() for _ in range(n)]
            for i in range(len(A) + 1):
                for j in range(len(B) + 1):
                    if 1 <= i + j:
                        c = [O[min(i + j, n) - 1]]
                        if i: c.append(-A[i - 1])
                        if j: c.append(-B[j - 1])
                        if i + j <= n or (i == 0 or j == 0 or True): s.cl.append(c)
                    if i + j < n:
                        c = [-O[i + j]]
                        if i < len(A): c.append(A[i])
                        if j < len(B): c.append(B[j])
                        s.cl.append(c)
            return O
        O = tot(lits) if lits else []
        if K is not None: O = O[:K]
        return [s.T] * nt + O
    @staticmethod
    def ge(o, k, T, F):  # literal for sum >= k
        if k <= 0: return T
        if k > len(o): return F
        return o[k - 1]
    def clause(s, c):
        if s.T in c: return
        s.cl.append([l for l in c if l != s.F])

def build(pat, sel=None, gen=(), fixed=(), U=False, tt=False, sb=False, nt=True, l4=True, l5=False, d1=True, extra=None):
    pts, _ = base_named(PAT[pat]); n = len(pts)
    core_pts, _ = base(PAT[pat]); W = witnesses(core_pts)
    if sel is not None: W = [W[k] for k in sel]
    e = Enc(); T, Fl = e.T, e.F
    inP = lambda a, i: i in pts[a][1]
    P = [[a for a in range(n) if inP(a, i)] for i in range(4)]
    N = {(i, j): [a for a in range(n) if inP(a, i) and inP(a, j)] for i, j in itertools.combinations(range(4), 2)}
    Tset = {Tr: [a for a in range(n) if pts[a][1] == frozenset(Tr)] for Tr in PAT[pat]}
    X = []
    for (i, j, x) in W:
        b = [e.pool.id(('x', i, j, x, a)) for a in range(n)]
        for a in N[i, j]: e.cl.append([b[a]] if a == x else [-b[a]])
        X.append(dict(b=b, pair=(i, j), x=x))
    for fi, fset in enumerate(fixed):   # constant edges (given as sets of point names), e.g. a solution being probed
        X.append(dict(b=[e.T if pts[a][0] in fset else e.F for a in range(n)], pair=None, x=None, gen=('fixed', fi), const=True))
    for gi, avoid in enumerate(gen):   # generic edges avoiding the named points 'avoid' (tau >= 5)
        b = [e.pool.id(('g', gi, a)) for a in range(n)]
        for a in range(n):
            if pts[a][0] in avoid: e.cl.append([-b[a]])
        X.append(dict(b=b, pair=None, x=None, gen=tuple(avoid)))
    ge = lambda o, k: Enc.ge(o, k, T, Fl)
    def le(o, k): return -ge(o, k + 1) if ge(o, k + 1) not in (T, Fl) else (Fl if ge(o, k + 1) == T else T)
    for F in X:
        if F.get('const'): continue
        b = F['b']; i, j = F['pair'] if F['pair'] else (None, None)
        e.clause([-ge(e.count(b, cap=22), 22)])
        for k in range(4):
            o = e.count([b[a] for a in P[k]], cap=6)
            e.clause([ge(o, 5)])
            if k in (i, j): e.clause([-ge(o, 6)])
        for kl, Nk in N.items():
            e.clause([b[a] for a in Nk])
            if d1:
                Bu = sorted(set(P[kl[0]]) | set(P[kl[1]]))
                o = e.count([b[a] for a in Bu], cap=10)
                # N not subset of F -> <= 9
                for a in Nk: e.clause([b[a], -ge(o, 10)])
        for Tr, t in PAT[pat].items():
            Bu = sorted(set().union(*[P[q] for q in Tr]))
            o = e.count([b[a] for a in Bu], cap=12)
            e.clause([b[a] for a in Tset[Tr]] + [-ge(o, 9 + t)])
    prodc = {}
    def prod(p, q, a):
        key = (p, q, a)
        if key not in prodc: prodc[key] = e.AND(X[p]['b'][a], X[q]['b'][a])
        return prodc[key]
    # per-edge unary counts on unions of base edges
    for F in X:
        F['cnt'] = {}
        for kl in N:
            F['cnt'][kl] = e.count([F['b'][a] for a in sorted(set(P[kl[0]]) | set(P[kl[1]]))], cap=19)
        for Tr in PAT[pat]:
            F['cnt'][Tr] = e.count([F['b'][a] for a in sorted(set().union(*[P[q] for q in Tr]))], cap=33)
    def sumbound(oF, oG, ov, bound, guard):
        # |F&B| + |G&B| + ov <= bound  (unless a guard literal holds)
        for i in range(0, len(oF) + 1):
            for j in range(0, len(oG) + 1):
                rest = bound - i - j
                if rest < 0:
                    # i + j > bound already impossible
                    pass
                lim = rest + 1   # ov >= lim forbidden
                if lim > len(ov): continue
                c = list(guard)
                if i: c.append(-ge(oF, i))
                if j: c.append(-ge(oG, j))
                if lim >= 1: c.append(-ge(ov, lim))
                e.clause(c)
    # (U) optional modelling of overlaps outside P0u..uP3 by unary LOWER-BOUND variables yu[p,q][k-1] = 'at least k
    # common U-points' (k=1..5); sound: every constraint below holds for the true values.
    yu = {}
    same = lambda F, G: F['pair'] is not None and F['pair'] == G['pair']
    if U:
        for p, q in itertools.combinations(range(len(X)), 2):
            F, G = X[p], X[q]
            if F.get('const') or G.get('const') or same(F, G): yu[p, q] = [Fl] * 5; continue
            vs = [e.new() for _ in range(5)]
            for k in range(4): e.cl.append([-vs[k + 1], vs[k]])
            yu[p, q] = vs
        Y = lambda p, q: yu[min(p, q), max(p, q)]
        for p, F in enumerate(X):
            if F.get('const'): continue
            groups = {}
            for q, G in enumerate(X):
                if q != p and G['pair'] is not None and not G.get('const'): groups.setdefault(G['pair'], []).append(q)
            for gp, qs in groups.items():   # cross-type singles of one base pair have pairwise disjoint U-parts
                lits = list(F['b']) + [l for q in qs for l in Y(p, q)]
                e.clause([-ge(e.count(lits, cap=22), 22)])
    for p, q in itertools.combinations(range(len(X)), 2):
        F, G = X[p], X[q]
        if F.get('const') and G.get('const'): continue
        pr = [prod(p, q, a) for a in range(n)]
        if U:
            ova = e.count(pr, cap=5)
            for j in range(5): e.clause([ge(ova, j + 1), yu[p, q][4 - j]])     # Lemma A: |F&G| >= 5
        for k in range(4): e.clause([pr[a] for a in P[k]])
        if l4:
            for (k, l), Nk in N.items():
                Bu = set(P[k]) | set(P[l])
                ov = e.count([pr[a] for a in range(n) if a not in Bu] + (yu[p, q] if U else []), cap=19)
                sumbound(F['cnt'][k, l], G['cnt'][k, l], ov, 18, [pr[a] for a in Nk])
        if l5:
            for Tr, t in PAT[pat].items():
                Bu = set().union(*[P[r] for r in Tr])
                ov = e.count([pr[a] for a in range(n) if a not in Bu], cap=33)
                sumbound(F['cnt'][Tr], G['cnt'][Tr], ov, 29 + t, [pr[a] for a in Tset[Tr]])
        if nt and F['pair'] is not None and F['pair'] == G['pair']:
            i, j = F['pair']
            for s_, o_ in ((i, j), (j, i)):
                o = e.count([pr[a] for a in P[s_] if not inP(a, o_)], cap=2)
                e.clause([ge(o, 2)])
    if U:   # F1 for three non-base edges: a common named point, or (if allowed) a common U-point
        for p, q, r in itertools.combinations(range(len(X)), 3):
            if all(X[t].get('const') for t in (p, q, r)): continue
            com = [e.AND(prod(p, q, a), X[r]['b'][a]) for a in range(n)]
            if same(X[p], X[q]) or same(X[p], X[r]) or same(X[q], X[r]): e.clause(com)
            else:
                for (x, y) in ((p, q), (p, r), (q, r)): e.clause(com + [yu[x, y][0]])
    if tt: add_tt(e, X, P, n, pts)
    if sb: add_sb(e, X, pts, n)
    if extra: extra(e, X, pts, P, N)
    return e, X, pts, W

def add_tt(e, X, P, n, pts):
    T, Fl = e.T, e.F
    ge = lambda o, k: Enc.ge(o, k, T, Fl)
    edges = [dict(b=[T if k in pts[a][1] else Fl for a in range(n)], base=k) for k in range(4)] + X
    for i in range(4):
        Xs = [x for x in edges if x.get('base') != i]
        e5 = []
        for x in Xs:
            o = e.count([x['b'][a] for a in P[i]], cap=6)
            if all(l in (T, Fl) for l in o):
                e5.append(T if sum(1 for l in o if l == T) == 5 else Fl)
            else:
                f = e.new(); g5, g6 = ge(o, 5), ge(o, 6)
                e.clause([-f, g5]); e.clause([-f, -g6]); e.clause([f, -g5, g6]); e5.append(f)
        z = {}; pr = {}
        for p, q in itertools.combinations(range(len(Xs)), 2):
            if Fl in (e5[p], e5[q]): continue
            ps = [e.AND(Xs[p]['b'][a], Xs[q]['b'][a]) for a in P[i]]
            pr[p, q] = ps
            o = e.count(ps, cap=2)
            g1, g2 = ge(o, 1), ge(o, 2)
            if g1 in (T, Fl) and g2 in (T, Fl): z[p, q] = T if (g1 == T and g2 == Fl) else Fl
            else:
                f = e.new(); e.clause([-f, g1]); e.clause([-f, -g2]); e.clause([f, -g1, g2]); z[p, q] = f
        for p, q, r in itertools.combinations(range(len(Xs)), 3):
            if all('base' in Xs[t] for t in (p, q, r)): continue
            if any(e5[t] == Fl for t in (p, q, r)): continue
            zz = [z.get(pq, Fl) for pq in ((p, q), (p, r), (q, r))]
            if Fl in zz: continue
            pre = [-l for l in [e5[p], e5[q], e5[r]] + zz if l != T]
            for ai, a in enumerate(P[i]):
                c = pre + [-pr[p, q][ai], Xs[r]['b'][a]]
                e.clause(c)

def add_sb(e, X, pts, n):
    """lex-sort columns within each O_i: column(a) >=lex column(a+1) (vectors over the new edges)."""
    for i in range(4):
        Oi = [a for a in range(n) if pts[a][0].startswith(f'O{i}_')]
        for a, c in zip(Oi, Oi[1:]):
            # lex: (x_1a,..,x_ma) >= (x_1c,...,x_mc); eq-prefix vars
            eq = e.T
            for F in X:
                A, C = F['b'][a], F['b'][c]
                # if prefix equal then A >= C
                e.clause([-eq, A, -C]) if eq != e.T else e.clause([A, -C])
                neq = e.new()  # neq -> eq & (A == C)
                e.cl += [[-neq, A, -C], [-neq, -A, C]]
                if eq != e.T: e.cl.append([-neq, eq])
                # completeness direction: eq & A==C -> neq
                e.cl.append([neq] + ([-eq] if eq != e.T else []) + [A, C])
                e.cl.append([neq] + ([-eq] if eq != e.T else []) + [-A, -C])
                eq = neq

def solve(pat, sel=None, cnf_out=None, drat_out=None, **kw):
    e, X, pts, W = build(pat, sel, **kw)
    t0 = time.time()
    if cnf_out:
        CNF(from_clauses=e.cl).to_file(cnf_out)
    s = Cadical153(bootstrap_with=e.cl, with_proof=bool(drat_out))
    r = s.solve()
    out = None
    if r:
        m = set(l for l in s.get_model() if l > 0)
        out = [((F['pair'], pts[F['x']][0] if F['x'] is not None else F.get('gen')), [pts[a][0] for a in range(len(pts)) if F['b'][a] in m]) for F in X]
    elif drat_out:
        with open(drat_out, 'w') as f:
            for line in s.get_proof(): f.write(line + '\n')
    return r, time.time() - t0, out, len(e.cl), e.pool.top

if __name__ == '__main__':
    pat = sys.argv[1]; selarg = sys.argv[2]; flags = sys.argv[3:]
    core_pts, _ = base(PAT[pat]); W = witnesses(core_pts)
    nm = lambda w: f"{w[0]}{w[1]}:{core_pts[w[2]][0]}"
    if selarg == 'all': sel = None
    elif selarg == 'apex0':
        sel = [k for k, w in enumerate(W) if (0 in w[:2] and len(core_pts[w[2]][1]) == 2) or (0 not in w[:2] and 0 not in core_pts[w[2]][1])]
    else: sel = [int(t) for t in selarg.split(',')]
    print(pat, [nm(W[k]) for k in (sel if sel is not None else range(len(W)))], flags, flush=True)
    kw = dict(tt='tt' in flags, sb='sb' in flags, U='U' in flags)
    gj = next((f.split('=', 1)[1] for f in flags if f.startswith('gens=')), None)
    if gj: kw['gen'] = [tuple(g) for g in json.loads(gj)]
    for f in flags:
        if f.startswith('no'): kw[f[2:]] = False
    cnf = next((f.split('=')[1] for f in flags if f.startswith('cnf=')), None)
    drat = next((f.split('=')[1] for f in flags if f.startswith('drat=')), None)
    r, t, out, ncl, nv = solve(pat, sel, cnf_out=cnf, drat_out=drat, **kw)
    print('SAT' if r else 'UNSAT', f'{t:.1f}s clauses={ncl} vars={nv}', flush=True)
    if out:
        for o in out: print(o, flush=True)
