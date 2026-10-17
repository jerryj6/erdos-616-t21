"""Referee's independent encoding of the W7-I finite system, MINIMAL version:
only the facts the §7.4 hand proof claims to use (no S(b) inequality, no (O), no CP' for (P_a,P_b)).
Pure clauses built with itertools (no pysat CardEnc). Usage: python3 ref_w7_min.py [noA] [ncs=3] [drat]
Points of Q: x12=0,x13=1,x23=2; Q1={3,4,5}, Q2={6,7,8}, Q3={9,10,11}; Q*={12..20}. C0 labels 0..3."""
import sys, itertools as it
from pysat.solvers import Solver
args = sys.argv[1:]
useA = 'noA' not in args
ncs = 3 if 'ncs=3' in args else 4
xid = {frozenset((1,2)):0, frozenset((1,3)):1, frozenset((2,3)):2}
x = lambda i,j: xid[frozenset((i,j))]
Qi = {1:[3,4,5], 2:[6,7,8], 3:[9,10,11]}; Qs = list(range(12,21)); P = range(21)
ell = {i: {x(i,j) for j in (1,2,3) if j!=i} | set(Qi[i]) for i in (1,2,3)}
nv = [0]; cls = []
def new(): nv[0] += 1; return nv[0]
def atmost(lits, k):
    for s in it.combinations(lits, k+1): cls.append([-l for l in s])
def atleast(lits, k):
    if k <= 0: return
    for s in it.combinations(lits, len(lits)-k+1): cls.append(list(s))
# W^i_q
W = {}
for i in (1,2,3):
    for q in Qi[i]:
        allowed = [p for p in P if p not in ell[i]]          # A subset Q \ l_i, |A| = 4
        A = {p: new() for p in allowed}
        atmost(list(A.values()), 4); atleast(list(A.values()), 4)
        K = [new() for _ in range(4)]; e3 = new()
        # e3 -> exactly 3 of K ; not e3 -> all 4
        for c in range(4): cls.append([e3, K[c]])
        atleast(K, 3); cls.append([-e3] + [-k for k in K])
        W[i,q] = dict(A=A, K=K, e3=e3, i=i, q=q)
# Y^{ab}_c
Y = {}
for (a,b) in [(1,2),(1,3),(2,3)]:
    k = 6-a-b
    for c in range(ncs):
        t = {p: new() for p in P}
        cls += [[t[x(a,k)]], [t[x(b,k)]], [-t[x(a,b)]]]
        for p in Qi[k] + Qs: cls.append([-t[p]])
        s = [t[p] for p in Qi[a]+Qi[b]]; atleast(s, 3); atmost(s, 4)
        Y[a,b,c] = dict(t=t, a=a, b=b, k=k, c=c)
oin = {}
for yk, y in Y.items():
    for wk, w in W.items():
        o = new(); oin[yk,wk] = o
        cls.append([-o, w['e3']])                 # o_W exists only if e = 3
        i, q = w['i'], w['q']; t = y['t']; Kc = w['K'][y['c']]
        # CP': if q notin Y:  #{p notin l_i u {q}: p in Y, p notin A} <= [c in K_W] + [o_W in Y] - 1
        cls.append([t[q], Kc, o])                 # bound -1 impossible
        viol = []
        for p in P:
            if p in ell[i] or p == q: continue
            Ap = w['A'].get(p)                    # p in Q\l_i so always in A's domain
            viol.append((t[p], Ap))
        for (tp, Ap) in viol:                      # bound 0 unless both K and o
            cls.append([t[q], -tp, Ap, Kc]); cls.append([t[q], -tp, Ap, o])
        for (tp, Ap), (tp2, Ap2) in it.combinations(viol, 2):   # bound <= 1 always
            cls.append([t[q], -tp, Ap, -tp2, Ap2])
if useA:
    for wk, w in W.items():
        k = w['i']; a, b = [j for j in (1,2,3) if j != k]
        atmost([oin[(a,b,c), wk] for c in range(ncs)], 1)
s = Solver(name='cadical153', bootstrap_with=cls, with_proof=('drat' in args))
r = s.solve()
print('useA', useA, 'ncs', ncs, 'vars', nv[0], 'clauses', len(cls), '->', 'SAT' if r else 'UNSAT')
if 'drat' in args and not r:
    with open('ref_w7_min.cnf','w') as f:
        f.write('p cnf %d %d\n' % (nv[0], len(cls)))
        for c in cls: f.write(' '.join(map(str,c)) + ' 0\n')
    with open('ref_w7_min.drat','w') as f:
        for l in s.get_proof(): f.write(l + '\n')
    print('wrote ref_w7_min.cnf / .drat')
