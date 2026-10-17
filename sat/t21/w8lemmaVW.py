"""Check of Lemma VW (Wave 8): in a (3,2,1,1)-K4 every edge Z with v,w notin Z has
 (i) m >= 1 + max(o2,o3)   (ii) al + ga >= m + 1 + o0 + o1 - min(o2,o3)
(m=|Z&m3|, al=|Z&alpha|, ga=|Z&gamma|, o_k=|Z&O_k|).  Uses only Lemma A (|Z&P_k|>=5) and L3 for T012={v}, T013={w}.
Region-count CP-SAT: search for a violation; INFEASIBLE = lemma holds (exact for these constraints)."""
import sys
sys.path.append("work/e616/pylib")
from ortools.sat.python import cp_model
for which in ('i', 'ii'):
    md = cp_model.CpModel(); V = lambda ub: md.NewIntVar(0, ub, '')
    m, al, ga, a3, a4, c3, c4 = V(3), V(2), V(3), V(2), V(2), V(1), V(1)
    o = [V(10), V(11), V(12), V(12)]; u = V(21)
    md.Add(m + al + ga + a3 + a4 + c3 + c4 + sum(o) + u == 21)
    P0 = m + al + a3 + a4 + o[0]; P1 = m + ga + c3 + c4 + o[1]; P2 = al + ga + a3 + c3 + o[2]; P3 = al + ga + a4 + c4 + o[3]
    for P in (P0, P1, P2, P3): md.Add(P >= 5)
    U012 = m + al + a3 + a4 + o[0] + ga + c3 + c4 + o[1] + o[2]; U013 = m + al + a3 + a4 + o[0] + ga + c3 + c4 + o[1] + o[3]
    md.Add(U012 <= 9); md.Add(U013 <= 9)
    mx = md.NewIntVar(0, 12, ''); md.AddMaxEquality(mx, [o[2], o[3]]); mn = md.NewIntVar(0, 12, ''); md.AddMinEquality(mn, [o[2], o[3]])
    if which == 'i': md.Add(m < 1 + mx)
    else: md.Add(al + ga < m + 1 + o[0] + o[1] - mn)
    s = cp_model.CpSolver(); print('violation of', which, ':', s.StatusName(s.Solve(md)))
