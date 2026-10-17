"""Trace-system SAT over all 5-subsets of an n-set: boolean per 5-subset. T1 intersecting, T2 closure
(every member and every point of it has a tangent member meeting it exactly there), T3 no triangle.
Seed: tau={0..4}, tau1={0,5,6,7,8}, tau2={1}+(4-set meeting {5..8} in a points).  Usage: tracefam.py n a"""
import sys, itertools
sys.path.append("work/e616/pylib")
from pysat.solvers import Cadical153
n, a = int(sys.argv[1]), int(sys.argv[2])
S = [frozenset(c) for c in itertools.combinations(range(n), 5)]
idx = {s: i + 1 for i, s in enumerate(S)}
cl = []
for s, t in itertools.combinations(S, 2):
    if not (s & t): cl.append([-idx[s], -idx[t]])
# T2
by_pt_sets = {}
for s in S:
    for x in s:
        tang = [idx[t] for t in S if s & t == {x}]
        cl.append([-idx[s]] + tang)
# T3: triangles
cnt = 0
single = {}
for s in S:
    single[s] = [t for t in S if len(s & t) == 1]
for s in S:
    for t in single[s]:
        if idx[t] <= idx[s]: continue
        for u in single[t]:
            if idx[u] <= idx[t]: continue
            if len(s & u) == 1 and not (s & t & u):
                cl.append([-idx[s], -idx[t], -idx[u]]); cnt += 1
seed = [frozenset(range(5)), frozenset({0, 5, 6, 7, 8}), frozenset({1} | set(range(9 - a, 13 - a)))]
for s in seed: cl.append([idx[s]])
sol = Cadical153(bootstrap_with=cl); r = sol.solve()
print(f'n={n} a={a} sets={len(S)} triangles={cnt}', 'SAT' if r else 'UNSAT', flush=True)
if r:
    m = set(x for x in sol.get_model() if x > 0)
    fam = [sorted(s) for s in S if idx[s] in m]; print(len(fam), fam[:60])
