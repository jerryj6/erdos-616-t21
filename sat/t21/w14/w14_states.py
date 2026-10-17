"""Wave 14: ALL feasible (core trace, o-vector) states of one new edge against the (3,2,1,1)-K4 base.
Uses w13_enum.check (the S13.1 single-edge constraint set). Rigorous enumeration box:
 o_i >= L_i = max(0,5-|b&P_i|) (Lemma A); o_i <= U_i = min(OSZ_i, 21-|b|-sum_{j!=i}L_j (CAP),
 9-|b&(P_i u P_j)|-L_j for every pair with N_ij not<= b (D1), 8+|t|-|b&U3|-sum_{q in T,q!=i}L_q for T∋i with b&t={} (L3)).
Every o violating the box violates a constraint of check(), so the box contains every feasible o."""
import sys, json, itertools
sys.path.insert(0, '..')
from w13_enum import *
feas = json.load(open('../w13_feas.json'))
def box(b):
    L = [max(0, 5 - pc(b & P[i])) for i in range(4)]
    U = []
    for i in range(4):
        u = min(OSZ[i], 21 - pc(b) - sum(L[j] for j in range(4) if j != i))
        for j in range(4):
            if j == i: continue
            Nij = N[tuple(sorted((i, j)))]
            if (b & Nij) != Nij: u = min(u, 9 - pc(b & (P[i] | P[j])) - L[j])
        for T, t in TRI.items():
            if i in T and not b & t:
                u = min(u, 8 + pc(t) - pc(b & (P[T[0]] | P[T[1]] | P[T[2]])) - sum(L[q] for q in T if q != i))
        U.append(u)
    return L, U
if __name__ == '__main__':
    out = []; boxsz = 0
    for b in feas:
        L, U = box(b)
        sts = []
        for o in itertools.product(*[range(L[i], U[i] + 1) for i in range(4)]):
            boxsz += 1
            if not check(b, list(o)): sts.append(list(o))
        assert sts, b
        out.append([b, sts])
    print('traces', len(out), 'states', sum(len(s) for _, s in out), 'box points', boxsz)
    json.dump(out, open('w14_states.json', 'w'))
