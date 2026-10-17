"""Wave 13 N-K4: exhaustive ONE-NEW-EDGE enumeration against the (3,2,1,1)-K4 base P0..P3.
An edge X is described by its core trace b (subset of the 16 core points) and o_i = |X & O_i|.
Constraints (all PROVED lemmas; every family has exactly one non-base edge, so everything is named):
 F1   X meets every N_ij                                        (F1 / R.1)
 A    |X&P_i| >= 5                                               (Lemma A)
 CAP  |b| + sum o <= 21
 L3   X & T_ijk = {}  =>  |X&(P_i u P_j u P_k)| <= 8 + t_ijk       (N.0(ii) = L on {P_i,P_j,P_k,X})
 D1   N_ij not<= X     =>  |X&(P_i u P_j)| <= 9                   (D1)
 W7b  X single of (P_i,P_j) of type x, P_k base single of type y != x: a>=2 and c>=2   (W7-I, no triangle)
 derived 5-pair (P_i,X) (|X&P_i| = 5, N = X&P_i):
   R3d  a base P_j with |P_j & N| = 1 has |P_j & X| = 5          (R.3; singles of >=2 types exist: R.2)
   D1d  a base P_j with N not<= P_j has |P_j & (P_i u X)| <= 9   (D1)
   W7d  two base singles P_j,P_k of (P_i,X) of different types: a=|T_ijk \\ b| != 1 and c=|b&(P_j&P_k)\\P_i| != 1
   SAd  two base singles of different types: (P_j&P_k) \\ (P_i u X) = {}   (S(a))
Completeness of o-search: o_i in {L_i, L_i+1}, L_i = max(0,5-|b&P_i|) (all other constraints monotone, see W13 notes).
"""
import itertools, json, sys
NAMES = ['v','w','al0','al1','g0','g1','g2','m0','m1','m2','a3_0','a3_1','a4_0','a4_1','c3','c4']
W8 = ['T012_0','T013_0','T023_0','T023_1','T123_0','T123_1','T123_2','p01_0','p01_1','p01_2','p02_0','p02_1','p03_0','p03_1','p12_0','p13_0']
MEM = [{0,1,2},{0,1,3},{0,2,3},{0,2,3},{1,2,3},{1,2,3},{1,2,3},{0,1},{0,1},{0,1},{0,2},{0,2},{0,3},{0,3},{1,2},{1,3}]
OSZ = [10, 11, 12, 12]
n = 16
P = [sum(1 << a for a in range(n) if i in MEM[a]) for i in range(4)]
pc = lambda x: bin(x).count('1')
PAIRS = list(itertools.combinations(range(4), 2))
N = {(i, j): P[i] & P[j] for i, j in PAIRS}
TRI = {T: P[T[0]] & P[T[1]] & P[T[2]] for T in itertools.combinations(range(4), 3)}

def bits(x): return [a for a in range(n) if x >> a & 1]
def nm(x): return '{' + ','.join(NAMES[a] for a in bits(x)) + '}'

def base_single(k, i, j):
    """type of base edge P_k as single of base pair (i,j), or None"""
    s = P[k] & N[(i, j)]
    return s if pc(s) == 1 else None

def check(b, o):
    """return list of violated constraint tags (empty = feasible)"""
    bad = []
    xi = [pc(b & P[i]) + o[i] for i in range(4)]
    if sum(o) + pc(b) > 21: bad.append('CAP')
    for i in range(4):
        if xi[i] < 5: bad.append(f'A{i}')
    for (i, j), Nij in N.items():
        if not b & Nij: bad.append(f'F1{i}{j}')
        if (b & Nij) != Nij and xi[i] + xi[j] - pc(b & Nij) > 9: bad.append(f'D1{i}{j}')
    for T, t in TRI.items():
        if not b & t:
            u = pc(b & (P[T[0]] | P[T[1]] | P[T[2]])) + sum(o[q] for q in T)
            if u > 8 + pc(t): bad.append(f'L3{T}')
    # W7 at base pairs
    for (i, j), Nij in N.items():
        s = b & Nij
        if pc(s) != 1: continue
        for k in range(4):
            if k in (i, j): continue
            y = base_single(k, i, j)
            if y is None or y == s: continue
            a = pc(b & P[k] & P[i] & ~Nij); c = pc(b & P[k] & P[j] & ~Nij)
            if a < 2 or c < 2: bad.append(f'W7b{i}{j}{k}')
    # derived pairs (P_i, X)
    for i in range(4):
        if xi[i] != 5: continue
        Nd = b & P[i]   # O_i points of X also lie in N but in no other P_j
        sing = []
        for j in range(4):
            if j == i: continue
            if pc(P[j] & Nd) == 1:
                sing.append(j)
                if xi[j] != 5: bad.append(f'R3d{i}{j}')
            full = (o[i] == 0 and (Nd & ~P[j]) == 0)
            if not full and 5 + pc(b & P[j] & ~P[i]) + o[j] > 9: bad.append(f'D1d{i}{j}')
        for j, k in itertools.combinations(sing, 2):
            if (P[j] & Nd) == (P[k] & Nd): continue
            a = pc(TRI[tuple(sorted((i, j, k)))] & ~b)
            c = pc(b & P[j] & P[k] & ~P[i])
            if a == 1 or c == 1: bad.append(f'W7d{i}{j}{k}')
            if (P[j] & P[k] & ~P[i] & ~b): bad.append(f'SAd{i}{j}{k}')
    return bad

def ovecs(b):
    L = [max(0, 5 - pc(b & P[i])) for i in range(4)]
    for d in itertools.product((0, 1), repeat=4):
        o = [L[i] + d[i] for i in range(4)]
        if all(o[i] <= OSZ[i] for i in range(4)): yield o

def feasible(b):
    return any(not check(b, o) for o in ovecs(b))

def all_o(b, maxo=None):
    """full enumeration of feasible o vectors (for reporting)"""
    out = []
    rng = [range(0, OSZ[i] + 1) for i in range(4)]
    for o in itertools.product(*rng):
        if sum(o) + pc(b) > 21: continue
        if not check(b, list(o)): out.append(o)
    return out

if __name__ == '__main__':
    feas = [b for b in range(1 << n) if all(b & Nij for Nij in N.values()) and feasible(b)]
    print('feasible core traces', len(feas))
    json.dump(feas, open('w13_feas.json', 'w'))
