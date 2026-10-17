"""Pure trace system on E1 (21 points): a family of k 5-subsets ('traces' E1&X of 5-pair partners X of E1) with
 T1 pairwise intersecting (F1: E1,X,Y have a common point),
 T2 closed: for every trace t and point x in t some trace t' has t&t' = {x} (R.2 + R.3: the single of type x of
    the 5-pair (E1,X) meets E1 in exactly 5),
 T3 no triangle: no three traces pairwise meeting in exactly one point with empty common intersection (Case N).
 seeded with M={0..4}, tG={0}+A_G, tH={1}+A_H, |A_G&A_H| = a.   Usage: python tracesys.py a k"""
import sys, itertools
sys.path.append("work/e616/pylib")
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
a, k = int(sys.argv[1]), int(sys.argv[2]); n = 21
pool = IDPool(); cl = []
X = [[pool.id(('x', i, p)) for p in range(n)] for i in range(k)]
def card(lits, kk, kind='eq'):
    f = {'eq': CardEnc.equals, 'le': CardEnc.atmost, 'ge': CardEnc.atleast}[kind]
    cl.extend(f(lits=lits, bound=kk, vpool=pool, encoding=EncType.seqcounter).clauses)
for i in range(k): card(X[i], 5)
I = {}
for i, j in itertools.combinations(range(k), 2):
    v = []
    for p in range(n):
        t = pool.id(('I', i, j, p)); cl += [[-t, X[i][p]], [-t, X[j][p]], [t, -X[i][p], -X[j][p]]]; v.append(t)
    I[i, j] = I[j, i] = v
    cl.append(v)  # T1
    # single-point indicator s_ij : |t_i & t_j| == 1  (s -> atmost1 ; not s -> atleast2)
    s = pool.id(('s', i, j))
    for c in CardEnc.atmost(lits=v, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses: cl.append([-s] + c)
    for c in CardEnc.atleast(lits=v, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses: cl.append([s] + c)
# T3: no triangle: s_ij & s_jk & s_ik -> common point exists (impossible when all pairwise single unless same point)
for i, j, l in itertools.combinations(range(k), 3):
    com = []
    for p in range(n):
        t = pool.id(('c3', i, j, l, p)); cl += [[-t, X[i][p]], [-t, X[j][p]], [-t, X[l][p]]]; com.append(t)
    cl.append([-pool.id(('s', i, j)), -pool.id(('s', j, l)), -pool.id(('s', i, l))] + com)
# T2: for each i, p: X[i][p] -> OR_j (t_i & t_j == {p})
for i in range(k):
    for p in range(n):
        ors = []
        for j in range(k):
            if j == i: continue
            d = pool.id(('d', i, p, j)); ors.append(d)
            cl.append([-d, I[i, j][p]]); cl.append([-d, pool.id(('s', min(i, j), max(i, j)))])
        cl.append([-X[i][p]] + ors)
seed = [set(range(5)), {0, 5, 6, 7, 8}, {1} | set(range(9 - a, 13 - a))]
for i, S in enumerate(seed):
    for p in range(n): cl.append([X[i][p] if p in S else -X[i][p]])
s = Cadical153(bootstrap_with=cl); r = s.solve()
print(f'a={a} k={k}', 'SAT' if r else 'UNSAT', flush=True)
if r:
    m = set(x for x in s.get_model() if x > 0)
    for i in range(k): print(i, sorted(p for p in range(n) if X[i][p] in m))
