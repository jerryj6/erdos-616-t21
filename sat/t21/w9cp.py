r"""Wave 9: CP-SAT version of the w9lazy model (same constraint instances, same semantics, linear encodings).
Used for the CEGAR search (memory-light); an UNSAT is certified by re-encoding the instances in CNF (w9lazy /
w9cert.py) and checking a DRAT proof with drat-trim.  u[p,q] = min(|F_p & F_q & U|, CAP) (exact up to CAP).
Instance semantics are documented in w9lazy.py."""
import sys, os, itertools
sys.path.append("work/e616/pylib")
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from ortools.sat.python import cp_model
from w9lazy import base_k4, base_nok4, find_violations, needed_edges, fivepairs, gen_of, CAP
import json

class CPM:
    def __init__(s, names, B, nk=False, gmax=2, acts=False):
        s.names, s.B, s.nk, s.gmax = names, B, nk, gmax
        s.n = len(names); s.m = cp_model.CpModel()
        s.edges = []; s.inst = []; s.instset = set(); s.u = {}; s.pr = {}; s.acts = acts; s.actlits = []
        s.one = s.m.NewConstant(1); s.zero = s.m.NewConstant(0)
    def bits(s, p):
        if p < 0: return [s.one if a in s.B[-1 - p] else s.zero for a in range(s.n)]
        return s.edges[p]['x']
    def add_edge(s, avoid, gen, label):
        m = s.m; x = [m.NewBoolVar('') for _ in range(s.n)]
        idx = len(s.edges); s.edges.append(dict(label=label, avoid=sorted(avoid), gen=gen, x=x))
        for a in avoid: m.Add(x[a] == 0)
        m.Add(sum(x) <= 21)
        for Bk in s.B: m.Add(sum(x[a] for a in Bk) >= 5)
        nb = len(s.B)
        for r in range(2, nb + 1):
            for S in itertools.combinations(range(nb), r):
                I = frozenset.intersection(*[s.B[k] for k in S]); U = frozenset.union(*[s.B[k] for k in S])
                b = len(U) - 40
                if b >= 21: continue
                g = s.avoid_lit([x[a] for a in sorted(I)])
                m.Add(sum(x[a] for a in U) <= b).OnlyEnforceIf(g)
        for k, l in itertools.combinations(range(nb), 2):
            N = s.B[k] & s.B[l]
            if len(N) != 5: continue
            # D1: N not subset of F -> |F & (Pk u Pl)| <= 9 ; encode: for each a in N: x[a]==0 -> sum <= 9
            for a in N: m.Add(sum(x[b] for b in (s.B[k] | s.B[l])) <= 9).OnlyEnforceIf(x[a].Not())
        return idx
    def avoid_lit(s, lits):
        """bool g with: (all lits false) -> g, and g -> all lits false."""
        lits = [l for l in lits if l is not s.zero]
        if any(l is s.one for l in lits): return s.zero_b()
        g = s.m.NewBoolVar('')
        for l in lits: s.m.AddImplication(g, l.Not())
        s.m.AddBoolOr([g] + lits)
        return g
    def zero_b(s):
        if not hasattr(s, '_zb'): s._zb = s.m.NewBoolVar(''); s.m.Add(s._zb == 0)
        return s._zb
    def AND(s, a, b):
        if a is s.zero or b is s.zero: return s.zero
        if a is s.one: return b
        if b is s.one: return a
        k = (min(a.Index(), b.Index()), max(a.Index(), b.Index()))
        if k not in s.pr:
            z = s.m.NewBoolVar(''); s.m.AddImplication(z, a); s.m.AddImplication(z, b); s.m.AddBoolOr([z, a.Not(), b.Not()])
            s.pr[k] = z
        return s.pr[k]
    def U(s, p, q):
        if p < 0 or q < 0: return 0
        k = (min(p, q), max(p, q))
        if k not in s.u: s.u[k] = s.m.NewIntVar(0, CAP, '')
        return s.u[k]
    def ind(s, expr, lo, hi, ub):
        """bool t with  (lo <= expr <= hi) -> t   (t may be true otherwise; used only as a guard premise)."""
        t = s.m.NewBoolVar(''); lt = s.m.NewBoolVar(''); gt = s.m.NewBoolVar('')
        # not t -> (expr < lo or expr > hi)
        s.m.AddBoolOr([t, lt, gt])
        s.m.Add(expr <= lo - 1).OnlyEnforceIf(lt)
        s.m.Add(expr >= hi + 1).OnlyEnforceIf(gt)
        return t
    def add_inst(s, ins):
        key = json.dumps(ins)
        if key in s.instset: return False
        s.instset.add(key); s.inst.append(ins)
        act = None
        if s.acts: act = s.m.NewBoolVar(''); s.actlits.append(act)
        s.encode(ins, act); return True
    def encode(s, ins, act):
        m = s.m; kind = ins[0]; E = [act] if act is not None else []
        def req(c): c.OnlyEnforceIf(E) if E else None
        if kind == 'LA':
            p, q = ins[1], ins[2]; X, Y = s.bits(p), s.bits(q)
            c = m.Add(sum(s.AND(X[a], Y[a]) for a in range(s.n)) + s.U(p, q) >= 5); req(c)
        elif kind == 'L2':
            p, q, S = ins[1], ins[2], ins[3]; X, Y = s.bits(p), s.bits(q)
            I = frozenset.intersection(*[s.B[k] for k in S]); Un = frozenset.union(*[s.B[k] for k in S])
            g = s.avoid_lit([s.AND(X[a], Y[a]) for a in sorted(I)])
            expr = sum(X[a] for a in Un) + sum(Y[a] for a in Un) + sum(s.AND(X[a], Y[a]) for a in range(s.n) if a not in Un) + s.U(p, q)
            m.Add(expr <= len(Un) - 19).OnlyEnforceIf([g] + E)
        elif kind == 'F1t':
            p, q, r = ins[1], ins[2], ins[3]; X, Y, Z = s.bits(p), s.bits(q), s.bits(r)
            com = [s.AND(s.AND(X[a], Y[a]), Z[a]) for a in range(s.n)]
            g = s.avoid_lit(com)
            for (u, v) in ((p, q), (p, r), (q, r)): m.Add(s.U(u, v) >= 1).OnlyEnforceIf([g] + E)
        elif kind == 'TT':
            Xs = sorted(s.B[ins[1]]); bb = [s.bits(p) for p in ins[2]]
            pre = [s.ind(sum(b[a] for a in Xs), 5, 5, 21) for b in bb]
            for i, j in itertools.combinations(range(3), 2):
                pre.append(s.ind(sum(s.AND(bb[i][a], bb[j][a]) for a in Xs), 1, 1, 21))
            com = [s.AND(s.AND(bb[0][a], bb[1][a]), bb[2][a]) for a in Xs]
            m.AddBoolOr(com).OnlyEnforceIf(pre + E)
        elif kind in ('NKg', 'NTCg'):
            _, p, q, z1, z2 = ins
            if kind == 'NKg': Q = sorted(s.B[-1 - p]); Y = s.bits(q)
            else: Q = sorted(s.B[-1 - q]); Y = s.bits(p)
            A, Bv = s.bits(z1), s.bits(z2)
            pre = [s.ind(sum(Y[a] for a in Q), 5, 5, 21)]
            for b in (A, Bv): pre.append(s.ind(sum(s.AND(Y[a], b[a]) for a in Q), 1, 1, 21))
            pre.append(s.avoid_lit([s.AND(s.AND(A[a], Bv[a]), Y[a]) for a in Q]))
            if kind == 'NKg':
                m.Add(sum(s.AND(A[a], Bv[a]) for a in range(s.n)) + s.U(z1, z2) >= 6).OnlyEnforceIf(pre + E)
            else:
                ex = []
                for a in Q:
                    ab = s.AND(A[a], Bv[a])
                    if Y[a] is s.one: continue
                    if Y[a] is s.zero: ex.append(ab); continue
                    w = m.NewBoolVar(''); m.AddImplication(w, ab); m.AddImplication(w, Y[a].Not()); m.AddBoolOr([w, ab.Not(), Y[a]]); ex.append(w)
                m.Add(sum(ex) >= 2).OnlyEnforceIf(pre + E)
        elif kind == 'NK':
            _, p, q, z1, z2, N = ins
            X, Y, A, Bv = s.bits(p), s.bits(q), s.bits(z1), s.bits(z2)
            pre = []
            # premise: N inside X and Y, no other common named point, no common U-point
            for a in N: pre += [X[a], Y[a]]
            pre.append(s.avoid_lit([s.AND(X[a], Y[a]) for a in range(s.n) if a not in N]))
            if p >= 0 and q >= 0:
                z = m.NewBoolVar(''); m.Add(s.U(p, q) == 0).OnlyEnforceIf(z); m.Add(s.U(p, q) >= 1).OnlyEnforceIf(z.Not()); pre.append(z)
            for b in (A, Bv): pre.append(s.ind(sum(b[a] for a in N), 1, 1, 5))
            pre.append(s.avoid_lit([s.AND(A[a], Bv[a]) for a in N]))
            pre = [l for l in pre if l is not s.one]
            if any(l is s.zero for l in pre): return
            m.Add(sum(s.AND(A[a], Bv[a]) for a in range(s.n)) + s.U(z1, z2) >= 6).OnlyEnforceIf(pre + E)
        elif kind == 'CAP':
            p, gs = ins[1], ins[2]; X = s.bits(p)
            pre = []
            for g, h in itertools.combinations(gs, 2):
                z = m.NewBoolVar(''); m.Add(s.U(g, h) == 0).OnlyEnforceIf(z); m.Add(s.U(g, h) >= 1).OnlyEnforceIf(z.Not()); pre.append(z)
            m.Add(sum(X) + sum(s.U(p, g) for g in gs) <= 21).OnlyEnforceIf(pre + E)
        else: raise ValueError(kind)
    def solve(s, tl=600, hint=None, workers=2):
        sv = cp_model.CpSolver(); sv.parameters.max_time_in_seconds = tl; sv.parameters.num_workers = workers
        if s.acts: s.m.ClearAssumptions(); s.m.AddAssumptions(s.actlits)
        s.m.ClearHints()
        if hint is not None:
            hs, hy = hint
            for e, S in zip(s.edges, hs):
                for a in range(s.n): s.m.AddHint(e['x'][a], 1 if a in S else 0)
            for k, v in hy.items():
                if k in s.u: s.m.AddHint(s.u[k], v)
        st = sv.Solve(s.m)
        s.status = sv.StatusName(st)
        if st == cp_model.INFEASIBLE:
            if s.acts:
                idx = set(sv.SufficientAssumptionsForInfeasibility())
                s.core = [i for i, l in enumerate(s.actlits) if l.Index() in idx]
            return None
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return 'UNKNOWN'
        sol = [frozenset(a for a in range(s.n) if sv.Value(e['x'][a])) for e in s.edges]
        yu = {k: sv.Value(v) for k, v in s.u.items()}
        return sol, yu
    def edgeset(s, sol, p): return s.B[-1 - p] if p < 0 else sol[p]
