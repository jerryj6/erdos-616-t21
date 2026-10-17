"""REFEREE (independent): per-edge state enumeration for the (3,2,1,1)-K4 base, written from the lemma statements.
Imports nothing from w13_/w14_. Base built from the triple structure: T123 (3 pts), T023 (2), T012 (1), T013 (1);
pair-private parts sized so every |P_i & P_j| = 5. Bit order is fixed by the authors' NAMES list only so traces can be
compared (the order is a labelling, not a computation).
A state = (b, o0..o3): b = core trace, o_q = |X & O_q|, u = 21-|b|-sum(o) >= 0 points outside all base edges.
Rules (each a proved lemma for ANY non-base edge X):
 F1  X meets every P_i & P_j (3 edges share a point)
 A   |X & P_i| >= 5
 L3  X misses T_ijk -> L on {P_i,P_j,P_k,X}: 48+|T| + 21 - |X&(Pi u Pj u Pk)| >= 61
 D1  N_ij not inside X -> |X & (P_i u P_j)| <= 9
 NTb X single of base pair (i,j) and P_k base single of (i,j) of another type -> |A-parts meet| >=2, |C-parts meet| >=2 (W7-I)
 derived 5-pair (P_i, X), N = X & P_i (|N| = 5):
   R3  base P_j with |P_j & N| = 1 is a single -> |P_j & X| = 5
   D1' base P_j with N not inside P_j -> |P_j & (P_i u X)| <= 9
   NT' two base singles of different types -> a != 1, c != 1 (W7-I; authors use only this part, a>=1 etc. not used)
   SA' two base singles of different types -> no common point outside P_i u X (S(a))
"""
import itertools, json, sys
NAMES = ['v','w','al0','al1','g0','g1','g2','m0','m1','m2','a3_0','a3_1','a4_0','a4_1','c3','c4']
REG = {'v': (0,1,2), 'w': (0,1,3), 'al': (0,2,3), 'g': (1,2,3), 'm': (0,1), 'a3': (0,2), 'a4': (0,3), 'c3': (1,2), 'c4': (1,3)}
def region(name):
    for k in ('a3', 'a4', 'c3', 'c4', 'al', 'g', 'm', 'v', 'w'):
        if name.startswith(k): return k
IN = [set(REG[region(x)]) for x in NAMES]
OSZ = [21 - sum(1 for a in range(16) if q in IN[a]) for q in range(4)]
Pm = [sum(1 << a for a in range(16) if q in IN[a]) for q in range(4)]
pc = lambda x: bin(x).count('1')
PR = list(itertools.combinations(range(4), 2))
def sanity():
    assert OSZ == [10, 11, 12, 12], OSZ
    for i, j in PR: assert pc(Pm[i] & Pm[j]) == 5
    tr = sorted(pc(Pm[i] & Pm[j] & Pm[k]) for i, j, k in itertools.combinations(range(4), 3))
    assert tr == [1, 1, 2, 3] and (Pm[0] & Pm[1] & Pm[2] & Pm[3]) == 0
sanity()
def ok(b, o):
    if min(o) < 0 or any(o[q] > OSZ[q] for q in range(4)) or pc(b) + sum(o) > 21: return False
    x = [pc(b & Pm[q]) + o[q] for q in range(4)]
    if min(x) < 5: return False
    for i, j in PR:
        Nij = Pm[i] & Pm[j]
        if b & Nij == 0: return False
        if (b & Nij) != Nij and x[i] + x[j] - pc(b & Nij) > 9: return False
    for T in itertools.combinations(range(4), 3):
        t = Pm[T[0]] & Pm[T[1]] & Pm[T[2]]
        if b & t: continue
        U = Pm[T[0]] | Pm[T[1]] | Pm[T[2]]
        if pc(b & U) + sum(o[q] for q in T) > 8 + pc(t): return False
    for i, j in PR:
        Nij = Pm[i] & Pm[j]
        if pc(b & Nij) != 1: continue
        for k in range(4):
            if k in (i, j): continue
            y = Pm[k] & Nij
            if pc(y) != 1 or y == (b & Nij): continue
            # A-part of X on P_i side: X & P_i \ N; of P_k: P_k & P_i \ N (core only; O_i points are not in P_k)
            if pc(b & Pm[k] & Pm[i] & ~Nij) < 2 or pc(b & Pm[k] & Pm[j] & ~Nij) < 2: return False
    for i in range(4):
        if x[i] != 5: continue
        Nc = b & Pm[i]          # core part of N = X & P_i; N also has o[i] points of O_i
        sing = []
        for j in range(4):
            if j == i: continue
            if pc(Pm[j] & Nc) == 1:
                sing.append(j)
                if x[j] != 5: return False
            Ninside = (o[i] == 0) and (Nc & ~Pm[j]) == 0
            if not Ninside and pc(Pm[j] & Pm[i]) + pc(b & Pm[j] & ~Pm[i]) + o[j] > 9: return False
        for j, k in itertools.combinations(sing, 2):
            if (Pm[j] & Nc) == (Pm[k] & Nc): continue
            # A-parts (P_i side): P_j & P_i \ N and P_k & P_i \ N  -> meet in T_ijk \ X
            a = pc(Pm[i] & Pm[j] & Pm[k] & ~b)
            # C-parts (X side): P_j & X \ P_i and P_k & X \ P_i -> meet in X & P_j & P_k \ P_i (core)
            c = pc(b & Pm[j] & Pm[k] & ~Pm[i])
            if a == 1 or c == 1: return False
            if Pm[j] & Pm[k] & ~Pm[i] & ~b: return False
    return True
def states(b):
    out = []
    L = [max(0, 5 - pc(b & Pm[q])) for q in range(4)]
    H = [min(OSZ[q], 21 - pc(b) - (sum(L) - L[q])) for q in range(4)]
    for o in itertools.product(*[range(L[q], H[q] + 1) for q in range(4)]):
        if ok(b, o): out.append(o)
    return out
if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    res = {}
    for b in range(lo, hi):
        if any(b & Pm[i] & Pm[j] == 0 for i, j in PR): continue
        s = states(b)
        if s: res[b] = s
    json.dump(res, open(f'ref_states_{lo}_{hi}.json', 'w'))
    print(lo, hi, len(res), sum(len(s) for s in res.values()))
