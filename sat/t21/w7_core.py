r"""W7 core finite model (independent CP-SAT re-encoding of the part of M3 that is needed).
Points of Q: x12=0, x13=1, x23=2, Q1={3,4,5}, Q2={6,7,8}, Q3={9,10,11}, Q*={12..20}.  C0 = {0,1,2,3} (labels c).
Edges: W[k,q] (k=1..3, q in Q_k): A-part A (4-subset of Q \ l_k), e in {3,4}, m (missing C0 label if e=3), o (exists iff e=3).
       Y[a,b,c]: Q-trace.  oin[Y,W] = (o_W in Y).
Constraints:
 (W)  |A & l_j| >= 1, and >= 2 if e = 3                          [W7-2 / Lemma S(b) vs P_j]
 (Y)  x_ak, x_bk in Y; x_ab, Q_k, Q_* not in Y; 3 <= |Y&(Q_a u Q_b)| <= 4   [Tri-2]
 (CP) for W = W[i,q] and Y with q notin Y:  |Y \ (l_i u {q} u A)| <= [c in K_W] + oin[Y,W] - 1     [W7-5 with (P_i,W)]
 (A)  for W of index k and the complementary pair (a,b): sum_c oin[Y[a,b,c],W] <= 1          [Lemma S(a) at (P_a,P_b)]
 (O)  oin[Y,W] -> e_W = 3;  if W has index a in {a,b} of Y: oin -> |Y & Q_a| <= 2          [|Y&O_a| = 3-|Y&Q_a|]
Usage: python3 w7_core.py [extra-claim-name]
"""
import sys, itertools
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model
X = {(1,2): 0, (1,3): 1, (2,3): 2}
Qi = {1: [3,4,5], 2: [6,7,8], 3: [9,10,11]}; Qs = list(range(12, 21)); PTS = range(21)
x = lambda i, j: X[tuple(sorted((i, j)))]
ell = {i: set([x(i, j) for j in (1,2,3) if j != i] + Qi[i]) for i in (1,2,3)}
def build(extra=None, useA=True, ncs=4):
    m = cp_model.CpModel()
    W = {}
    for k in (1,2,3):
        for q in Qi[k]:
            A = {p: m.NewBoolVar('') for p in PTS}
            for p in ell[k]: m.Add(A[p] == 0)
            m.Add(sum(A.values()) == 4)
            e3 = m.NewBoolVar(''); K = [m.NewBoolVar('') for c in range(4)]
            m.Add(sum(K) == 3).OnlyEnforceIf(e3); m.Add(sum(K) == 4).OnlyEnforceIf(e3.Not())
            for j in (1,2,3):
                if j == k: continue
                m.Add(sum(A[p] for p in ell[j]) >= 1); m.Add(sum(A[p] for p in ell[j]) >= 2).OnlyEnforceIf(e3)
            W[k, q] = dict(A=A, e3=e3, K=K, k=k, q=q)
    Y = {}
    for (a, b) in [(1,2), (1,3), (2,3)]:
        k = 6 - a - b
        for c in range(ncs):
            t = {p: m.NewBoolVar('') for p in PTS}
            m.Add(t[x(a, k)] == 1); m.Add(t[x(b, k)] == 1); m.Add(t[x(a, b)] == 0)
            for p in Qi[k] + Qs: m.Add(t[p] == 0)
            s = sum(t[p] for p in Qi[a] + Qi[b]); m.Add(s >= 3); m.Add(s <= 4)
            Y[a, b, c] = dict(t=t, a=a, b=b, k=k, c=c)
    oin = {}
    for yk, y in Y.items():
        for wk, w in W.items():
            o = m.NewBoolVar(''); oin[yk, wk] = o
            m.AddImplication(o, w['e3'])
            if w['k'] in (y['a'], y['b']):
                m.Add(sum(y['t'][p] for p in Qi[w['k']]) <= 2).OnlyEnforceIf(o)
            # (CP)
            i, q = w['k'], w['q']
            outs = []
            for p in PTS:
                if p in ell[i] or p == q: continue
                v = m.NewBoolVar(''); outs.append(v)
                # v = t[p] and not A[p]
                m.AddBoolAnd([y['t'][p], w['A'][p].Not()]).OnlyEnforceIf(v)
                m.AddBoolOr([y['t'][p].Not(), w['A'][p]]).OnlyEnforceIf(v.Not())
            act = y['t'][q].Not()
            m.Add(sum(outs) <= w['K'][y['c']] + o - 1).OnlyEnforceIf(act)
    for wk, w in W.items():
        k = w['k']; a, b = [i for i in (1,2,3) if i != k]
        if useA: m.Add(sum(oin[(a, b, c), wk] for c in range(ncs)) <= 1)
    if extra: extra(m, W, Y, oin)
    return m
def run(extra=None, tl=100, **kw):
    m = build(extra, **kw); s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 2
    return s.StatusName(s.Solve(m))
if __name__ == '__main__':
    print('core model:', run())
    print('control without (A):', run(useA=False))
    print('control with only 3 values of c:', run(ncs=3))
