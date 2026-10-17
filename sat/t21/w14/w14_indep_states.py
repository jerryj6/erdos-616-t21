"""INDEPENDENT re-implementation (sets, no import of w13_enum/w14_*) of the single-edge constraints of S13.1, written from the
lemma statements, and comparison with w14_states.json. A state accepted here but missing there would be a potential
over-rejection (unsoundness) of w13_enum.check.
Edge X = core trace b (subset of 16 core points) + o_q = |X & O_q| (O_q = private part of P_q, sizes 10,11,12,12) + U-part.
 F1   X meets every N_ij = P_i & P_j.            A    |X & P_i| >= 5.          CAP  |b| + sum o <= 21.
 L3   L on {P_i,P_j,P_k,X} when X misses T_ijk:  |P_i u P_j u P_k u X| >= 61 (exact union count).
 D1   at the base 5-pair (P_i,P_j): N_ij not inside X  =>  |X & (P_i u P_j)| <= 9.
 W7   X single of (P_i,P_j) of type x and base edge P_k single of (P_i,P_j) of type y != x: a = |X & P_k & (P_i \\ P_j)| >= 2,
      c = |X & P_k & (P_j \\ P_i)| >= 2.
 Derived 5-pair (P_i, X) with |X & P_i| = 5, N = X & P_i:
   R3d  base P_j with |P_j & N| = 1  =>  |P_j & X| = 5.
   D1d  base P_j with N not inside P_j  =>  |P_j & (P_i u X)| <= 9.
   W7d  base singles P_j, P_k of (P_i,X) of different types: |P_j&P_k&(P_i\\X)| != 1 and |P_j&P_k&(X\\P_i)| != 1.
   SAd  same: (P_j & P_k) \\ (P_i u X) empty."""
import itertools, json
MEM = [{0,1,2},{0,1,3},{0,2,3},{0,2,3},{1,2,3},{1,2,3},{1,2,3},{0,1},{0,1},{0,1},{0,2},{0,2},{0,3},{0,3},{1,2},{1,3}]
OSZ = [10, 11, 12, 12]
PB = [frozenset(a for a in range(16) if i in MEM[a]) for i in range(4)]
def ok(b, o):
    X = b; xi = [len(X & PB[i]) + o[i] for i in range(4)]
    if len(X) + sum(o) > 21: return False
    if any(v < 5 for v in xi): return False
    for i, j in itertools.combinations(range(4), 2):
        N = PB[i] & PB[j]
        if not (X & N): return False
        if not N <= X and len(X & (PB[i] | PB[j])) + o[i] + o[j] > 9: return False
    for T in itertools.combinations(range(4), 3):
        t = PB[T[0]] & PB[T[1]] & PB[T[2]]
        if X & t: continue
        U3 = PB[T[0]] | PB[T[1]] | PB[T[2]]
        union = len(U3) + sum(OSZ[q] for q in T) + len(X - U3) + sum(o[q] for q in range(4) if q not in T) + (21 - len(X) - sum(o))
        if union < 61: return False
    for i, j in itertools.combinations(range(4), 2):
        N = PB[i] & PB[j]; s = X & N
        if len(s) != 1: continue
        for k in range(4):
            if k in (i, j): continue
            y = PB[k] & N
            if len(y) != 1 or y == s: continue
            a = len(X & PB[k] & (PB[i] - PB[j])); c = len(X & PB[k] & (PB[j] - PB[i]))
            if a < 2 or c < 2: return False
    for i in range(4):
        if xi[i] != 5: continue
        Ncore = X & PB[i]
        sing = []
        for j in range(4):
            if j == i: continue
            if len(PB[j] & Ncore) == 1:
                sing.append(j)
                if xi[j] != 5: return False
            inside = (o[i] == 0 and Ncore <= PB[j])
            if not inside and len(PB[j] & PB[i]) + len((X & PB[j]) - PB[i]) + o[j] > 9: return False
        for j, k in itertools.combinations(sing, 2):
            if (PB[j] & Ncore) == (PB[k] & Ncore): continue
            JK = PB[j] & PB[k]
            if len(JK & (PB[i] - X)) == 1 or len(JK & (X - PB[i])) == 1: return False
            if JK - PB[i] - X: return False
    return True
def ubound(b, L):
    """o_i upper bounds read off CAP and D1 (both stated above), so the scan box contains every accepted o."""
    U = []
    for i in range(4):
        u = min(OSZ[i], 21 - len(b) - sum(L) + L[i])
        for j in range(4):
            if j == i: continue
            N = PB[i] & PB[j]
            if not N <= b: u = min(u, 9 - len(b & (PB[i] | PB[j])) - L[j])
        U.append(u)
    return U
if __name__ == '__main__':
    import os
    CK = 'w14_indep_states_ck.json'
    ck = json.load(open(CK)) if os.path.exists(CK) else {'next': 0, 'mine': {}}
    mine = {int(k): set(map(tuple, v)) for k, v in ck['mine'].items()}
    for start in range(ck['next'], 1 << 16, 2048):
        for bm in range(start, start + 2048):
            b = frozenset(a for a in range(16) if bm >> a & 1)
            if not all(b & PB[i] & PB[j] for i, j in itertools.combinations(range(4), 2)): continue
            L = [max(0, 5 - len(b & PB[i])) for i in range(4)]
            U = ubound(b, L)
            for o in itertools.product(*[range(L[i], U[i] + 1) for i in range(4)]):
                if ok(b, o): mine.setdefault(bm, set()).add(tuple(o))
        ck = {'next': start + 2048, 'mine': {k: sorted(v) for k, v in mine.items()}}
        json.dump(ck, open(CK + '.tmp', 'w')); os.replace(CK + '.tmp', CK)
    ref = {b: set(map(tuple, s)) for b, s in json.load(open('w14_states.json'))}
    extra = sum(len(mine.get(b, set()) - ref.get(b, set())) for b in mine)
    fewer = sum(len(ref[b] - mine.get(b, set())) for b in ref)
    print('indep traces', len(mine), 'states', sum(map(len, mine.values())), '| w14 traces', len(ref), 'states', sum(map(len, ref.values())))
    print('states accepted here but NOT in w14_states (potential over-rejection):', extra)
    print('states in w14_states rejected here:', fewer)
    print('DONE')
