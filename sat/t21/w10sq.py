r"""Wave 10: SQUEEZE instances for the w9lazy U-mode model (monkeypatch; import after w9lazy).
[SQ] (W, V, [G_1..G_k]) all new edges.  If the G_j have pairwise no common U-point and no (W,V,G_j) has a common
named point, then |W & V & U| >= k.   Proof: F1 gives u_j in W&V&G_j; it is not named, so u_j in U, and the u_j are
distinct because G_j & G_j' & U = {}.  Combined with L2 (= OO at a base 5-pair) this is Lemma SQ of Wave 10."""
import itertools, w9lazy
from w9lazy import Model, CAP
_old_encode = Model.encode
def encode(s, ins):
    if ins[0] != 'SQ': return _old_encode(s, ins)
    _, w, v, gs = ins; X, Yb = s.bits(w), s.bits(v)
    cl = [s.Y(g, h)[0] for g, h in itertools.combinations(gs, 2)]
    for g in gs:
        Z = s.bits(g); cl += [s.AND(s.AND(X[a], Yb[a]), Z[a]) for a in range(s.n)]
    cl.append(s.Y(w, v)[min(len(gs), CAP) - 1])
    s.add(cl, 'SQ')
Model.encode = encode
_old_fv = w9lazy.find_violations
def find_violations(md, sol, yu, limit=400):
    out = _old_fv(md, sol, yu, limit)
    U = lambda p, q: yu.get((min(p, q), max(p, q)), 0)
    n = len(sol); cnt = 0
    for w, v in itertools.combinations(range(n), 2):
        I = sol[w] & sol[v]
        T = [g for g in range(n) if g not in (w, v) and not (I & sol[g])]
        T.sort(key=lambda g: sum(1 for h in T if h != g and U(g, h) == 0), reverse=True)
        grp = []
        for g in T:
            if all(U(g, h) == 0 for h in grp): grp.append(g)
        grp = grp[:CAP]
        if len(grp) > U(w, v):
            out.append(['SQ', w, v, grp]); cnt += 1
    return out
w9lazy.find_violations = find_violations

# ---------------------------------------------------------------------------------------------------------------
# [SF] (P base, X1, X2, X3 new, drop pair (a,b)).  L on {P,X1,X2,X3}: if P&X1&X2&X3 = {} (P has no U-point, so this
# is a statement about named points) then |X1 u X2 u X3 \ P| >= 40, i.e. (|Xi| = 21)
#   sum_{named a not in P} ([m_a >= 2] + [m_a >= 3]) + sum_{pairs} |Xi&Xj&U| - |X1&X2&X3&U| + sum_i |Xi & P| <= 23,
# m_a = multiplicity of a in X1,X2,X3.  Since |X1&X2&X3&U| <= |Xa&Xb&U| we may drop both terms (valid, weaker):
#   sum_a(...) + (U-overlaps of the two other pairs) + sum_i |Xi&P| <= 23.
def _sf_encode(s, ins):
    _, P, ts, drop = ins; P = s.B[P]
    X = [s.bits(t) for t in ts]
    lits = []
    for a in range(s.n):
        if a in P:
            lits += [X[0][a], X[1][a], X[2][a]]
        else:
            ab, ac, bc = s.AND(X[0][a], X[1][a]), s.AND(X[0][a], X[2][a]), s.AND(X[1][a], X[2][a])
            m2 = s.newv()
            for l in (ab, ac, bc): s.add([-l, m2], 'def')
            s.add([-m2, ab, ac, bc], 'def')
            lits += [m2, s.AND(ab, X[2][a])]
    for (i, j) in itertools.combinations(range(3), 2):
        if sorted((ts[i], ts[j])) != sorted(drop): lits += s.Y(ts[i], ts[j])
    o = s.count(lits, 24)
    guard = [s.AND(s.AND(X[0][a], X[1][a]), X[2][a]) for a in sorted(P)]
    s.add(guard + [-s.ge(o, 24)], 'SF')
_enc2 = Model.encode
def encode2(s, ins):
    if ins[0] == 'SF': return _sf_encode(s, ins)
    return _enc2(s, ins)
Model.encode = encode2
_fv2 = w9lazy.find_violations
def find_violations2(md, sol, yu, limit=400):
    out = _fv2(md, sol, yu, limit)
    U = lambda p, q: yu.get((min(p, q), max(p, q)), 0)
    n = len(sol); B = md.B; k = 0
    for t in itertools.combinations(range(n), 3):
        X = [sol[i] for i in t]; tri = X[0] & X[1] & X[2]
        prs = list(itertools.combinations(t, 2)); drop = min(prs, key=lambda pq: U(*pq))
        for pi, P in enumerate(B):
            if tri & P: continue
            m2 = ((X[0] & X[1]) | (X[0] & X[2]) | (X[1] & X[2])) - P
            lhs = len(m2) + len(tri - P) + sum(U(*pq) for pq in prs if pq != drop) + sum(len(x & P) for x in X)
            if lhs > 23:
                out.append(['SF', pi, list(t), list(drop)]); k += 1
                if k > 300: return out
    return out
w9lazy.find_violations = find_violations2
find_violations = find_violations2
