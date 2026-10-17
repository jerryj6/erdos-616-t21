r"""Wave 12: local extension test (selection heuristic for tau-edges; soundness of any final UNSAT does NOT depend on it).
Given a literal realized family E (w10x_TAG_real.json) and a 4-set B of named points, decide (CP-SAT) whether one more
21-set Z with Z cap B = empty can be added satisfying a SUBSET of the proved constraints w.r.t. the fixed family:
  Lemma A (|Z cap X| >= 5), L on S u {Z} for every subfamily S with |US| <= 60, D1 and R3 at every 5-pair (X,Y) of E,
  SA and W7 between Z and existing singles of every 5-pair of E.
Z may use existing points and any number of fresh points. 'non-extendable' (INFEASIBLE) means this realization cannot
survive adding the slot 'edge avoiding B' (nothing else moves) -> the slot is a genuine cut.
"""
import json, itertools, sys
from ortools.sat.python import cp_model

def subfams(E, cap=60):
    out = []
    def dfs(start, cur, U):
        for i in range(start, len(E)):
            U2 = U | E[i]
            if len(U2) <= cap:
                S = cur + [i]
                if len(S) >= 2: out.append((S, U2))
                dfs(i + 1, S, U2)
    dfs(0, [], frozenset())
    return out

class Ext:
    def __init__(self, edges):
        self.E = [frozenset(e) for e in edges]
        self.P = sorted(set().union(*self.E))
        self.sf = subfams(self.E)
        E = self.E; self.pairs = []
        for i, j in itertools.combinations(range(len(E)), 2):
            N = E[i] & E[j]
            if len(N) == 5:
                sing = {}
                for k in range(len(E)):
                    if k in (i, j): continue
                    t = E[k] & N
                    if len(t) == 1: sing.setdefault(next(iter(t)), []).append(k)
                self.pairs.append((i, j, N, sing))

    def extendable(self, B, tl=5.0):
        E = self.E; m = cp_model.CpModel()
        x = {p: m.NewBoolVar('') for p in self.P if p not in B}
        f = m.NewIntVar(0, 21, 'f')
        m.Add(sum(x.values()) + f == 21)
        def cnt(S): return sum(x[p] for p in S if p in x)
        for X in E: m.Add(cnt(X) >= 5)
        for S, U in self.sf:
            I = frozenset.intersection(*[E[i] for i in S]); lits = [x[p] for p in I if p in x]
            if len(U) - 40 >= 21: continue
            b = m.NewBoolVar('')
            if lits: m.AddBoolOr(lits).OnlyEnforceIf(b.Not())      # b false -> Z meets the common part
            else: m.Add(b == 1)
            m.Add(cnt(U) <= len(U) - 40).OnlyEnforceIf(b)
        for (i, j, N, sing) in self.pairs:
            X, Y = E[i], E[j]; XY = X | Y
            full = m.NewBoolVar('')   # N subset Z
            m.Add(cnt(N) == 5).OnlyEnforceIf(full); m.Add(cnt(N) <= 4).OnlyEnforceIf(full.Not())
            m.Add(cnt(XY) <= 9).OnlyEnforceIf(full.Not())                   # D1
            for y in N:
                if y not in x: continue
                sy = m.NewBoolVar('')   # Z is a single of type y
                m.Add(cnt(N) == 1).OnlyEnforceIf(sy); m.AddImplication(sy, x[y])
                ny = [x[p] for p in N if p != y and p in x]
                # sy <-> x[y] and no other N point
                m.AddBoolOr([x[y].Not()] + ny + [sy])
                for l in ny: m.AddImplication(sy, l.Not())
                m.Add(cnt(X) == 5).OnlyEnforceIf(sy); m.Add(cnt(Y) == 5).OnlyEnforceIf(sy)   # R3
                for y2, ks in sing.items():
                    if y2 == y: continue
                    for k in ks:
                        W = E[k]
                        for p in W - XY:
                            if p in x: m.AddImplication(sy, x[p].Not())                 # SA
                        m.Add(cnt((W & X) - N) >= 2).OnlyEnforceIf(sy)                 # W7 (both sides)
                        m.Add(cnt((W & Y) - N) >= 2).OnlyEnforceIf(sy)
        s = cp_model.CpSolver(); s.parameters.num_workers = 1; s.parameters.max_time_in_seconds = tl
        r = s.Solve(m)
        return {cp_model.OPTIMAL: True, cp_model.FEASIBLE: True, cp_model.INFEASIBLE: False}.get(r, None)

if __name__ == '__main__':
    R = json.load(open(sys.argv[1])); ex = Ext(R['edges'])
    print(len(ex.E), 'edges', len(ex.P), 'points', len(ex.sf), 'subfams<=60', len(ex.pairs), '5-pairs')
    for B in sys.argv[2:]:
        print(B, ex.extendable(frozenset(B.split('+'))))
