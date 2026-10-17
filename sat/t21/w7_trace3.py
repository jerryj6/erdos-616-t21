r"""Wave 7 trace model M3 (unconditional; relaxation of any counterexample containing a triangle).
Each modelled edge E has: Q-trace T[E] (21 booleans), C0-set K[E] (4 booleans), and for every W the boolean O[E,W] = "o_W in E"
(o_W = the unique point of W in O_i when |W&C0| = 3).  Edges: P1..P3; W^i_q (9); Y^{ab}_c (12); D_c (4, avoid x's and c).
Constraints (each a proved lemma, see candidates file §7):
 W^i_q: T = {q} u A, |T|=5, T&l_i={q}; |K| = e in {3,4}; |T&l_j| + e >= 5 (j != i);  O[W,W] = (e==3); O[E,W]=0 for P's and for
   W' of other index (W7-2: W' avoids O_i); O[W',W] free for same index.
 Y^{ab}_c: trace rules of Tri-2; K = {c}; O[Y,W^a] -> |Y&Q_a| <= 2 (|Y&O_a| = 3-|Y&Q_a|); same for b; O[Y,W^k] free.
 D_c: T inside Q1uQ2uQ3, 1<=|T&Q_i|<=2, sum>=5 (Tri-3); K = C0\c; O[D,W^i] -> |D&Q_i| <= 1 (|D&O_i| = 2-|D&Q_i|).
 CP' (W7-5) for pairs (P_a,P_b) [C=C0], (P_i,W^i_q) [C = K[W] u {o_W}], (P_j,W^i_q) if T[W]&l_j = {p} [C = C0]:
   every modelled F with p notin F: |T[F] \ (T1 u T2)| <= |F & C| - 1.
 Traces pairwise intersect.  Trace triangles (W7-1): if three modelled edges have 5-traces pairwise meeting in single points
   with no common point, then for each pair (a,b) and third c: K[a]&K[b] subset K[c], and O[a,W]&O[b,W] -> O[c,W].
"""
import itertools, sys, os
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
FL = set(os.environ.get('W7FLAGS', 'inter,cpcond,c3,D,cpW,A,Sd').split(','))
pool = IDPool(); cl = []
YP=[tuple(map(int,y)) for y in os.environ.get('W7Y','12,13,23').split(',')]
YC=[int(c) for c in os.environ.get('W7C','0,1,2,3').split(',')]
WI=[int(c) for c in os.environ.get('W7W','1,2,3').split(',')]
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
    if op == '==' and k > len(lits): return [[]]
    return f(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses
def card(lits, op, k): cl.extend(enc(op, lits, k))
def cardif(conds, lits, op, k):
    for c in enc(op, lits, k): cl.append([-d for d in conds] + c)
V = lambda *a: pool.id(a)
def AND(name, lits):
    g = V(*name); cl.append([g] + [-l for l in lits])
    for l in lits: cl.append([-g, l])
    return g
TRUE = V('TRUE'); cl.append([TRUE])
T, K, kind = {}, {}, {}
def new(n, kd):
    T[n] = {p: V('T', n, p) for p in PTS}; K[n] = [V('K', n, c) for c in range(4)]; kind[n] = kd
for i in (1,2,3):
    n = 'P%d' % i; new(n, ('P', i))
    for p in PTS: cl.append([T[n][p]] if p in ell[i] else [-T[n][p]])
    for c in range(4): cl.append([K[n][c]])
Ws = []
for i in WI:
    for q in Qi[i]:
        n = 'W%d_%d' % (i, q); Ws.append(n); new(n, ('W', i, q))
        cl.append([T[n][q]])
        for p in ell[i] - {q}: cl.append([-T[n][p]])
        card([T[n][p] for p in PTS], '==', 5)
        e3 = V('e3', n)
        if 'c3' not in FL: cl.append([-e3])
        cardif([e3], K[n], '==', 3); cardif([-e3], K[n], '==', 4)
        for j in (1,2,3):
            if j == i: continue
            lj = [T[n][p] for p in ell[j]]
            card(lj, '>=', 1); cardif([e3], lj, '>=', 2)
for (a, b) in YP:
    k = 6 - a - b
    for c in YC:
        n = 'Y%d%d_%d' % (a, b, c); new(n, ('Y', a, b, c))
        cl.append([T[n][x(a, k)]]); cl.append([T[n][x(b, k)]]); cl.append([-T[n][x(a, b)]])
        for p in Qi[k] + Qs: cl.append([-T[n][p]])
        card([T[n][p] for p in Qi[a] + Qi[b]], '>=', 3); card([T[n][p] for p in Qi[a] + Qi[b]], '<=', 4)
        for cc in range(4): cl.append([K[n][cc]] if cc == c else [-K[n][cc]])
if 'D' in FL:
    for c in range(4):
        n = 'D_%d' % c; new(n, ('D', c))
        for p in [0, 1, 2] + Qs: cl.append([-T[n][p]])
        for i in (1,2,3): card([T[n][p] for p in Qi[i]], '>=', 1); card([T[n][p] for p in Qi[i]], '<=', 2)
        card([T[n][p] for p in Qi[1] + Qi[2] + Qi[3]], '>=', 5)
        for cc in range(4): cl.append([K[n][cc]] if cc != c else [-K[n][cc]])
names = list(T)
O = {}
for E in names:
    for W in Ws:
        o = V('O', E, W); O[E, W] = o
        kE, kW = kind[E], kind[W]; iW = kW[1]
        cl.append([V('e3', W), -o])        # o_W exists only if e3
        if kE[0] == 'P':
            if kE[1] == iW: cl.append([o, -V('e3', W)])   # o_W in O_i subset P_i
            else: cl.append([-o])
        elif kE[0] == 'W':
            if E == W: cl.append([o, -V('e3', W)])
            elif kE[1] != iW: cl.append([-o])
        elif kE[0] == 'Y':
            a, b = kE[1], kE[2]
            if iW in (a, b): cardif([o], [T[E][p] for p in Qi[iW]], '<=', 2)
        elif kE[0] == 'D':
            cardif([o], [T[E][p] for p in Qi[iW]], '<=', 1)
def both(a, b, p):
    key = (a, b) if names.index(a) < names.index(b) else (b, a)
    return V('both', key[0], key[1], p)
for a, b in itertools.combinations(names, 2):
    for p in PTS:
        t = both(a, b, p); cl += [[-t, T[a][p]], [-t, T[b][p]], [t, -T[a][p], -T[b][p]]]
    if 'inter' in FL: cl.append([both(a, b, p) for p in PTS])

if 'A' in FL:
  pass
# (a) outside parts of Y^{ab}_c (c varying) are pairwise disjoint and O_k is outside P_a u P_b:
for (a, b) in ([(1,2), (1,3), (2,3)] if 'A' in FL else []):
    k = 6 - a - b
    for W in Ws:
        if kind[W][1] == k and (a,b) in YP: card([O['Y%d%d_%d' % (a, b, c), W] for c in YC], '<=', 1)
# (d) Lemma S at (Q,P_i) between W^i_q, W^i_q' (q != q'): |A&A'| + |C&C'| >= 5, |A&A'| = 1 -> C = C'.
for W, W2 in (itertools.combinations(Ws, 2) if 'Sd' in FL else []):
    if kind[W][1] != kind[W2][1]: continue
    cl.append([-O[W2, W], O[W, W2]]); cl.append([-O[W, W2], O[W2, W]]); cl.append([-O[W2, W], V('e3', W2)])
    kk = [AND(('kk', W, W2, c), [K[W][c], K[W2][c]]) for c in range(4)]
    card([both(W, W2, p) for p in PTS] + kk + [O[W2, W]], '>=', 5)
    # |A&A'| <= 1 -> K equal and o equal
    lits = [both(W, W2, p) for p in PTS]
    small = V('smallWW', W, W2)
    for cc in enc('>=', lits, 2): cl.append([small] + cc)   # not small -> >=2
    for c in range(4): cl += [[-small, -K[W][c], K[W2][c]], [-small, K[W][c], -K[W2][c]]]
    cl += [[-small, -V('e3', W), O[W2, W]], [-small, -V('e3', W2), O[W, W2]]]

# CP' pairs: (X1, X2, p, conds, Cdesc) ; Cdesc = ('C0',) or ('own', W)
pairs = []
for a, b in [(1,2), (1,3), (2,3)]: pairs.append(('P%d' % a, 'P%d' % b, x(a, b), [], ('C0',)))
for W in Ws:
    _, i, q = kind[W]
    pairs.append(('P%d' % i, W, q, [], ('own', W)))
    if 'cpcond' in FL:
        for j in (1,2,3):
            if j == i: continue
            for p in ell[j]:
                cond = V('cpc', W, j, p)
                cl.append([-cond, T[W][p]]); cardif([cond], [T[W][r] for r in ell[j]], '<=', 1)
                cl.append([cond, -T[W][p]] + [T[W][r] for r in ell[j] if r != p])
                pairs.append(('P%d' % j, W, p, [cond], ('C0',)))
Fs = [n for n in names if kind[n][0] in ('Y', 'D') or (kind[n][0] == 'W' and 'cpW' in FL)]
for F in Fs:
    for X1, X2, p, conds, Cd in pairs:
        if F in (X1, X2): continue
        outs = []
        for r in PTS:
            o = V('out', F, X1, X2, r)
            cl += [[-o, T[F][r]], [-o, -T[X1][r]], [-o, -T[X2][r]], [o, -T[F][r], T[X1][r], T[X2][r]]]
            outs.append(o)
        # inC lits: F & C ; C0 part
        if Cd[0] == 'C0': inC = list(K[F])
        else:
            W = Cd[1]; inC = [AND(('kc', F, W, c), [K[F][c], K[W][c]]) for c in range(4)] + [O[F, W]]
        # |outs| <= |inC| - 1   <=>  |outs| + |not inC| <= len(inC) - 1
        act = conds + [-T[F][p]]
        cardif(act, outs + [-l for l in inC], '<=', len(inC) - 1)
if 'tri' in FL:
    five = {}
    for n in names:
        f = V('five', n)
        if kind[n][0] == 'Y' or kind[n][0] == 'D':
            cardif([f], [T[n][p] for p in PTS], '<=', 5)
        five[n] = f if kind[n][0] in ('Y', 'D') else TRUE
    def one(a, b):
        g = V('one', *sorted((a, b)))
        cardif([g], [both(a, b, p) for p in PTS], '<=', 1)
        return g
    cnt = 0
    for a, b, c in itertools.combinations(names, 3):
        if kind[a][0] == 'P' and kind[b][0] == 'P' and kind[c][0] == 'P': continue
        g = [one(a, b), one(a, c), one(b, c), five[a], five[b], five[c]]
        nocom = V('nocom', a, b, c)
        for p in PTS: cl.append([-nocom, -both(a, b, p), -T[c][p]])
        tri = AND(('tri', a, b, c), g + [nocom])
        for (u, w, z) in [(a, b, c), (a, c, b), (b, c, a)]:
            for cc in range(4): cl.append([-tri, -K[u][cc], -K[w][cc], K[z][cc]])
            for W in Ws: cl.append([-tri, -O[u, W], -O[w, W], O[z, W]])
        cnt += 1
    print('triangle triples', cnt)
s = Cadical153(bootstrap_with=cl)
res = s.solve(); print('FLAGS', sorted(FL), 'SAT' if res else 'UNSAT', 'vars', pool.top, 'clauses', len(cl), flush=True)
if res:
    mdl = set(l for l in s.get_model() if l > 0)
    for n in names: print(n, sorted(p for p in PTS if T[n][p] in mdl), 'K', [c for c in range(4) if K[n][c] in mdl],
                          'o:', [W for W in Ws if O[n, W] in mdl])
if os.environ.get('W7CNF'):
    from pysat.formula import CNF
    CNF(from_clauses=cl).to_file(os.environ['W7CNF'])
