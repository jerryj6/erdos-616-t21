r"""Wave 7 trace model on Q (21 points), CONDITIONAL on hypothesis H4: every (Q,P_i)-single W of type q in Q_i has |W&C0|=4.
Variables: Q-traces of W^i_q (9 edges), Y^{ij} (one per base pair; the 4 values of c do not interact here), D (avoid x's, c).
Constraints (all proved in Wave 6/7 given H4):
 - W^i_q: trace = {q} u A, |trace|=5, A misses l_i, A meets l_j\{x_ij} and l_k\{x_ik} (W7-2 with c=4: a>=1).
 - C0-pairs: (P_i,P_j) through x_ij; (P_i,W^i_q) through q; (P_j,W^i_q) through p iff |A & l_j| = 1 (W & P_j = (A&l_j) u C0).
 - Y^{ij}: trace contains x_ik,x_jk; misses x_ij, Q_k, Q_*; |Y&Q_i|+|Y&Q_j| in {3,4} (Tri-2).
 - D: trace inside Q1uQ2uQ3, |D&Q_i| in {1,2}, sum >= 5 (Tri-3).
 - Lemma CP: C0-pair (X1,X2) through p, edge F with p notin F: |F&Q \ (t1 u t2)| <= z-1 (z=|F&C0|: Y 1, D 3).
 - all traces pairwise intersect (F1 with Q).
 - W7-1: a trace triangle {t(X1),t(X2),t(Y)} with X1,X2 containing C0 (P's, W's) and |t(Y)|=5 is impossible
   (the K4 would force Y to contain X1&X2\Q = C0).
"""
import itertools, sys, os
FL=set(os.environ.get('W7FLAGS','tri,cpD,cpY,cpcond,inter').split(','))
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
sys.setrecursionlimit(10000)
pool = IDPool(); cl = []
X = {(1,2): 0, (1,3): 1, (2,3): 2}
Qi = {1: [3,4,5], 2: [6,7,8], 3: [9,10,11]}; Qs = list(range(12, 21)); PTS = list(range(21))
def x(i, j): return X[tuple(sorted((i, j)))]
ell = {i: set([x(i, j) for j in (1,2,3) if j != i] + Qi[i]) for i in (1,2,3)}
def card(lits, op, k):
    f = {'==': CardEnc.equals, '>=': CardEnc.atleast, '<=': CardEnc.atmost}[op]
    cl.extend(f(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
def cardif(cond, lits, op, k):  # cond -> card
    f = {'==': CardEnc.equals, '>=': CardEnc.atleast, '<=': CardEnc.atmost}[op]
    for c in f(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses: cl.append([-cond] + c)
def fixed_trace(name, S):
    v = {p: pool.id((name, p)) for p in PTS}
    for p in PTS: cl.append([v[p]] if p in S else [-v[p]])
    return v
T = {}; z = {}; blocks = []
for i in (1,2,3):
    T['P%d' % i] = fixed_trace('P%d' % i, ell[i]); blocks.append('P%d' % i)
for i in (1,2,3):
    for q in Qi[i]:
        n = 'W%d_%d' % (i, q); v = {p: pool.id((n, p)) for p in PTS}; T[n] = v; blocks.append(n)
        cl.append([v[q]])
        for p in ell[i] - {q}: cl.append([-v[p]])
        card([v[p] for p in PTS], '==', 5)
        for j in (1,2,3):
            if j != i: cl.append([v[p] for p in ell[j] - {x(i, j)}])
YS=[tuple(map(int,y)) for y in os.environ.get('W7Y','12,13,23').split(',')]
for (i, j) in YS:
    k = 6 - i - j; n = 'Y%d%d' % (i, j); v = {p: pool.id((n, p)) for p in PTS}; T[n] = v; z[n] = 1
    cl.append([v[x(i, k)]]); cl.append([v[x(j, k)]]); cl.append([-v[x(i, j)]])
    for p in Qi[k] + Qs: cl.append([-v[p]])
    card([v[p] for p in Qi[i] + Qi[j]], '>=', 3); card([v[p] for p in Qi[i] + Qi[j]], '<=', 4)
v = {p: pool.id(('D', p)) for p in PTS}; T['D'] = v; z['D'] = 3
for p in [0,1,2] + Qs: cl.append([-v[p]])
for i in (1,2,3): card([v[p] for p in Qi[i]], '>=', 1); card([v[p] for p in Qi[i]], '<=', 2)
card([v[p] for p in Qi[1] + Qi[2] + Qi[3]], '>=', 5)
names = list(T)
# pairwise intersecting
for a, b in itertools.combinations(names, 2):
    ts = []
    if 'inter' not in FL: ts=None
    for p in PTS:
        t = pool.id(('both', a, b, p)); cl += [[-t, T[a][p]], [-t, T[b][p]], [t, -T[a][p], -T[b][p]]]
        if ts is not None: ts.append(t)
    if ts is not None: cl.append(ts)
def both(a, b, p):
    t = pool.id(('both', *sorted((a, b)), p))
    return t if (sorted((a, b)) == [a, b]) else pool.id(('both', b, a, p))
def inter(a, b, p):
    key = ('both', a, b, p) if names.index(a) < names.index(b) else ('both', b, a, p)
    return pool.id(key)
# C0-pair indicator cp[(a,b,p)]: a,b blocks, Q&a&b = {p}, a&b = C0 u {p}
cps = []
for i, j in [(1,2), (1,3), (2,3)]:
    cps.append(('P%d' % i, 'P%d' % j, x(i, j), None))  # unconditional
for i in (1,2,3):
    for q in Qi[i]:
        n = 'W%d_%d' % (i, q); cps.append(('P%d' % i, n, q, None))
        for j in (1,2,3):
            if j == i: continue
            for p in ell[j] - {x(i, j)}:
                # cond: A & l_j == {p}
                cond = pool.id(('cpc', n, j, p))
                lits = [T[n][r] for r in ell[j]]
                # cond <-> T[n][p] and sum(lits)==1
                cl.append([-cond, T[n][p]])
                cardif(cond, lits, '<=', 1)
                # reverse: T[n][p] and none other -> cond
                cl.append([cond, -T[n][p]] + [T[n][r] for r in ell[j] if r != p])
                if 'cpcond' in FL: cps.append(('P%d' % j, n, p, cond))
print('C0-pair candidates:', len(cps))
# Lemma CP on Y's and D
for F in [f for f in z if (f=='D' and 'cpD' in FL) or (f!='D' and 'cpY' in FL)]:
    for a, b, p, cond in cps:
        # if cond and p notin F: |F & Q \ (ta u tb)| <= z-1
        outs = []
        for r in PTS:
            o = pool.id(('out', F, a, b, p, r))
            # o <-> F[r] & !a[r] & !b[r]
            cl += [[-o, T[F][r]], [-o, -T[a][r]], [-o, -T[b][r]], [o, -T[F][r], T[a][r], T[b][r]]]
            outs.append(o)
        g = pool.id(('cpact', F, a, b, p))
        # g <- cond & !F[p]
        cl.append([g, T[F][p]] + ([-cond] if cond else []))
        cardif(g, outs, '<=', z[F] - 1)
# W7-1: trace triangle {X1,X2,Y} with X1,X2 blocks and |t(Y)|=5 impossible
for Yn in ['Y%d%d'%y for y in YS]:
    y5 = pool.id(('y5', Yn)); cardif(y5, [T[Yn][p] for p in PTS], '==', 5)
    cl.append([y5] + [-1])  if False else None
    # y5 <- sum==5 : encode via (sum<=5) -> y5 ; sum>=5 always (|Y&Q|>=5 holds automatically) so use atmost
    for cc in CardEnc.atleast(lits=[T[Yn][p] for p in PTS], bound=6, vpool=pool, encoding=EncType.seqcounter).clauses:
        pass
    a6 = pool.id(('y6', Yn))
    cardif(a6, [T[Yn][p] for p in PTS], '>=', 6); cl.append([y5, a6])
    for X1, X2 in itertools.combinations(blocks, 2):
        # pairwise single points and no common point: |X1&X2|=1, |X1&Y|=1, |X2&Y|=1, X1&X2&Y empty
        pairs = [(X1, X2), (X1, Yn), (X2, Yn)]
        ones = []
        for a, b in pairs:
            o = pool.id(('one', a, b)); ones.append(o)
            lits = [inter(a, b, p) for p in PTS]
            # o -> sum(lits) <= 1  (sum>=1 already)
            cardif(o, lits, '<=', 1)
            # sum<=1 -> o : if o false then sum>=2
            cardif(-o if False else pool.id(('none', a, b)), lits, '>=', 2); cl.append([o, pool.id(('none', a, b))])
        for p in PTS:
            # not all three ones, or p in common, ... forbid: ones all true and y5 and no common point
            pass
        common = []
        for p in PTS:
            cpv = pool.id(('com3', X1, X2, Yn, p)); common.append(cpv)
            cl += [[-cpv, T[X1][p]], [-cpv, T[X2][p]], [-cpv, T[Yn][p]]]
        if 'tri' in FL: cl.append([-o for o in ones] + [-y5] + common)
s = Cadical153(bootstrap_with=cl)
res = s.solve(); print('SAT' if res else 'UNSAT')
if res:
    m = set(l for l in s.get_model() if l > 0)
    for n in names: print(n, sorted(p for p in PTS if T[n][p] in m))
