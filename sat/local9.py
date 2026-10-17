"""Local model around a 9-set B (r=21, tau>=5): avoiders S_C=(B\\C) u D_C for every 4-subset C of B, D_C subset O.
Constraints (all valid consequences of L_21 + P1, derived in candidates/erdos-616-t21-construct.md):
 pairs: |D_C & D_C'| >= 5 - |B \\ (C u C')|
 covering triples C1,C2,C3 (union B): sum|D| - |union D| <= 8   [family {B,S1,S2,S3}, e<=23]
                                      D1&D2&D3 nonempty          [3-wise intersecting]
 9 <= |S_C| <= 20 -> 4 <= |D_C| <= 15.
Question: can |D_{C0}| >= 5 ?  usage: python3 local9.py o timeout"""
import sys
from itertools import combinations
from ortools.sat.python import cp_model
o = int(sys.argv[1]); TL = float(sys.argv[2])
B = range(9); Cs = [frozenset(c) for c in combinations(B, 4)]
m = cp_model.CpModel()
y = [[m.NewBoolVar(f"y{i}_{v}") for v in range(o)] for i in range(len(Cs))]
for i in range(len(Cs)):
    m.Add(sum(y[i]) >= 4)
for i, j in combinations(range(len(Cs)), 2):
    need = 5 - len(set(B) - (Cs[i] | Cs[j]))
    if need > 0:
        a = [m.NewBoolVar("") for v in range(o)]
        for v in range(o):
            m.AddImplication(a[v], y[i][v]); m.AddImplication(a[v], y[j][v])
        m.Add(sum(a) >= need)
nt = 0
for i, j, k in combinations(range(len(Cs)), 3):
    if len(Cs[i] | Cs[j] | Cs[k]) == 9:
        nt += 1
        w = [m.NewIntVar(0, 2, "") for v in range(o)]
        for v in range(o):
            m.Add(w[v] >= y[i][v] + y[j][v] + y[k][v] - 1)
        m.Add(sum(w) <= 8)
        a = [m.NewBoolVar("") for v in range(o)]
        for v in range(o):
            m.AddImplication(a[v], y[i][v]); m.AddImplication(a[v], y[j][v]); m.AddImplication(a[v], y[k][v])
        m.AddBoolOr(a)
i0 = Cs.index(frozenset({0, 1, 2, 3}))
for v in range(5):
    m.Add(y[i0][v] == 1)
s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = TL; s.parameters.num_workers = 1
st = s.Solve(m)
print("o", o, "triples", nt, s.StatusName(st), s.WallTime())
if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    for i, C in enumerate(Cs):
        print(sorted(C), [v for v in range(o) if s.Value(y[i][v])])
