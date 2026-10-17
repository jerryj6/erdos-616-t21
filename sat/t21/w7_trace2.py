r"""Wave 7 trace model M2 on Q (21 points), UNCONDITIONAL version (no H4).  All constraints are proved lemmas:
 * P_i traces l_i (Tri-0).
 * W^i_q (q in Q_i; (Q,P_i)-single of type q, exists by R.2): trace t = {q} u A, |t| = 5, t & l_i = {q};
   e = |W & C0| in {3,4}; if e = 3, W misses one point m in C0 and has one point o in O_i (W7-2);
   |t & l_j| + e >= 5 for j != i (W7-2, Lemma S(b)).
 * Y^{ab}_c for every base pair (a,b) and every c in C0 (R.2 at (P_a,P_b)): trace contains x_ak, x_bk, misses x_ab, Q_k, Q_*;
   |Y & Q_a| + |Y & Q_b| in {3,4} (Tri-2).  Y & C0 = {c}.  Membership of o_W in Y: free boolean (relaxation).
 * Lemma CP' (W7-5): if Q,X1,X2 pairwise meet in exactly 5 and Q&X1&X2 = {p}, then for every edge F not containing p:
   |F & Q \ (X1 u X2)| <= |F & (X1&X2) \ Q| - 1.   Pairs used: (P_a,P_b) [p = x_ab, X1&X2\Q = C0];
   (P_i, W^i_q) [p = q, X1&X2\Q = (W&C0) u (W&O_i)];  (P_j, W^i_q) when t & l_j = {p} [then e = 4, X1&X2\Q = C0].
   Applied to F = every Y.
 * Traces of any two edges meet (F1 with Q).
"""
import itertools, sys, os
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
FL = set(os.environ.get('W7FLAGS', 'inter,cpcond,c3').split(','))
CS = [int(c) for c in os.environ.get('W7C', '0,1,2,3').split(',')]
pool = IDPool(); cl = []
X = {(1,2): 0, (1,3): 1, (2,3): 2}
Qi = {1: [3,4,5], 2: [6,7,8], 3: [9,10,11]}; Qs = list(range(12, 21)); PTS = list(range(21))
def x(i, j): return X[tuple(sorted((i, j)))]
ell = {i: set([x(i, j) for j in (1,2,3) if j != i] + Qi[i]) for i in (1,2,3)}
def enc(op, lits, k):
    f = {'==': CardEnc.equals, '>=': CardEnc.atleast, '<=': CardEnc.atmost}[op]
    if op == '<=' and k < 0: return [[]]
    if op == '>=' and k <= 0: return []
    if op == '<=' and k >= len(lits): return []
    if op == '>=' and k > len(lits): return [[]]
    return f(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses
def card(lits, op, k): cl.extend(enc(op, lits, k))
def cardif(conds, lits, op, k):  # AND(conds) -> card
    for c in enc(op, lits, k): cl.append([-d for d in conds] + c)
V = lambda *a: pool.id(a)
T = {}
for i in (1,2,3):
    T['P%d' % i] = {p: V('P%d' % i, p) for p in PTS}
    for p in PTS: cl.append([T['P%d' % i][p]] if p in ell[i] else [-T['P%d' % i][p]])
Ws = []
for i in (1,2,3):
    for q in Qi[i]:
        n = 'W%d_%d' % (i, q); Ws.append((n, i, q)); T[n] = {p: V(n, p) for p in PTS}
        cl.append([T[n][q]])
        for p in ell[i] - {q}: cl.append([-T[n][p]])
        card([T[n][p] for p in PTS], '==', 5)
        e3 = V('e3', n)              # e = 3
        if 'c3' not in FL: cl.append([-e3])
        m = [V('m', n, c) for c in range(4)]   # missing C0 point (only if e3)
        for c in range(4): cl.append([e3, -m[c]])
        cl.append([-e3] + m); card(m, '<=', 1)
        for j in (1,2,3):
            if j == i: continue
            lj = [T[n][p] for p in ell[j]]
            card(lj, '>=', 1)               # e = 4 case
            cardif([e3], lj, '>=', 2)       # e = 3 case
Ys = []
for (a, b) in [(1,2), (1,3), (2,3)]:
    k = 6 - a - b
    for c in CS:
        n = 'Y%d%d_%d' % (a, b, c); Ys.append((n, a, b, c)); T[n] = {p: V(n, p) for p in PTS}
        cl.append([T[n][x(a, k)]]); cl.append([T[n][x(b, k)]]); cl.append([-T[n][x(a, b)]])
        for p in Qi[k] + Qs: cl.append([-T[n][p]])
        card([T[n][p] for p in Qi[a] + Qi[b]], '>=', 3); card([T[n][p] for p in Qi[a] + Qi[b]], '<=', 4)
names = list(T)
def both(a, b, p):
    key = (a, b) if names.index(a) < names.index(b) else (b, a)
    return V('both', key[0], key[1], p)
for a, b in itertools.combinations(names, 2):
    for p in PTS:
        t = both(a, b, p); cl += [[-t, T[a][p]], [-t, T[b][p]], [t, -T[a][p], -T[b][p]]]
    if 'inter' in FL: cl.append([both(a, b, p) for p in PTS])
# CP' pairs: (X1, X2, p, cond_lits, kind)
pairs = []
for a, b in [(1,2), (1,3), (2,3)]: pairs.append(('P%d' % a, 'P%d' % b, x(a, b), [], 'C0'))
for n, i, q in Ws:
    pairs.append(('P%d' % i, n, q, [], 'own'))
    if 'cpcond' in FL:
        for j in (1,2,3):
            if j == i: continue
            for p in ell[j]:
                cond = V('cpc', n, j, p)
                cl.append([-cond, T[n][p]]); cardif([cond], [T[n][r] for r in ell[j]], '<=', 1)
                cl.append([cond, -T[n][p]] + [T[n][r] for r in ell[j] if r != p])
                pairs.append(('P%d' % j, n, p, [cond], 'C0'))
for F, a, b, c in Ys:
    for X1, X2, p, conds, kind in pairs:
        outs = []
        for r in PTS:
            o = V('out', F, X1, X2, r)
            cl += [[-o, T[F][r]], [-o, -T[X1][r]], [-o, -T[X2][r]], [o, -T[F][r], T[X1][r], T[X2][r]]]
            outs.append(o)
        act = conds + [-T[F][p]]   # active when conds hold and p notin F
        if kind == 'C0':
            cardif(act, outs, '<=', 0)          # |F & C0| = 1
        else:
            W = X2; e3 = V('e3', W); oin = V('oin', F, W)   # o_W in F (free)
            # |F & C| = [e=4] + [e=3]*([c != m] + [o in F])
            cardif(act + [-e3], outs, '<=', 0)
            # e=3, m = c: bound = oin - 1
            cardif(act + [e3, V('m', W, c), -oin], outs, '<=', -1)
            cardif(act + [e3, V('m', W, c), oin], outs, '<=', 0)
            # e=3, m != c: bound = oin
            cardif(act + [e3, -V('m', W, c), -oin], outs, '<=', 0)
            cardif(act + [e3, -V('m', W, c), oin], outs, '<=', 1)
s = Cadical153(bootstrap_with=cl)
res = s.solve(); print('FLAGS', sorted(FL), 'C', CS, 'SAT' if res else 'UNSAT', 'vars', pool.top, 'clauses', len(cl))
if res:
    mdl = set(l for l in s.get_model() if l > 0)
    for n in names: print(n, sorted(p for p in PTS if T[n][p] in mdl), 'e3' if V('e3', n) in mdl else '')
if os.environ.get('W7CNF'):
    from pysat.formula import CNF
    CNF(from_clauses=cl).to_file(os.environ['W7CNF'])
