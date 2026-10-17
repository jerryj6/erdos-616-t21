"""INDEPENDENT re-check of conflict clauses (does not import w14_compat, w14_group, or w13_enum's check).
For a trace pair (t,t') declared conflicting, every state pair (from w14_states.json) is tested by EXPLICIT enumeration of all
integer overlaps z_q = |F&F'&O_q| (q=0..3) and zU = |F&F'&U| against the literal statements of the rules:
 A: |F&F'| >= 5;  F1: {P_q,F,F'} share a point;  L: for every set X of >=2 base edges with (cap X) & F & F' = {},
 |U X  u F u F'| >= 61 (exact union count);  SAME (cross-type singles of base pair (i,j)): S(a) no common point outside
 P_i u P_j, NT a>=2, c>=2, S(b) a+c>=5;  D1 at a derived 5-pair (P_k,F): if F&P_k has 5 points and is not inside F', then
 |F' & (P_k u F)| <= 9 (and symmetrically).
Usage: python3 w14_indep.py PAIRFILE.npy SAMPLE SEED  -> reports pairs whose some state pair admits a feasible z (= disagreement)."""
import sys, json, itertools, random, numpy as np
NAMES = ['v','w','al0','al1','g0','g1','g2','m0','m1','m2','a3_0','a3_1','a4_0','a4_1','c3','c4']
MEM = [{0,1,2},{0,1,3},{0,2,3},{0,2,3},{1,2,3},{1,2,3},{1,2,3},{0,1},{0,1},{0,1},{0,2},{0,2},{0,3},{0,3},{1,2},{1,3}]
OSZ = [10, 11, 12, 12]
CORE = frozenset(range(16))
PB = [frozenset(a for a in range(16) if i in MEM[a]) for i in range(4)]
def S(b): return frozenset(a for a in range(16) if b >> a & 1)
def feasible_pair(b1, o1, b2, o2):
    B1, B2 = S(b1), S(b2); I = B1 & B2
    u1 = 21 - len(B1) - sum(o1); u2 = 21 - len(B2) - sum(o2)
    same = []
    for i, j in itertools.combinations(range(4), 2):
        Nij = PB[i] & PB[j]
        x, y = B1 & Nij, B2 & Nij
        if len(x) == 1 and len(y) == 1 and x != y: same.append((i, j))
    rng = [range(max(0, o1[q] + o2[q] - OSZ[q]), min(o1[q], o2[q]) + 1) for q in range(4)]
    for z in itertools.product(*rng):
        for zU in range(0, min(u1, u2) + 1):
            ok = True
            if len(I) + sum(z) + zU < 5: ok = False
            for q in range(4):
                if ok and not (I & PB[q]) and z[q] == 0: ok = False
            for (i, j) in same:
                if not ok: break
                if (I - PB[i] - PB[j]) or any(z[q] for q in range(4) if q not in (i, j)) or zU: ok = False; break
                a = len(I & (PB[i] - PB[j])) + z[i]; c = len(I & (PB[j] - PB[i])) + z[j]
                if a < 2 or c < 2 or a + c < 5: ok = False
            for r in (2, 3, 4):
                if not ok: break
                for X in itertools.combinations(range(4), r):
                    capX = CORE
                    for q in X: capX = capX & PB[q]
                    if capX & I: continue
                    cupX = frozenset().union(*[PB[q] for q in X])
                    ux = len(cupX) + sum(OSZ[q] for q in X)
                    f1 = len(B1 - cupX) + sum(o1[q] for q in range(4) if q not in X) + u1
                    f2 = len(B2 - cupX) + sum(o2[q] for q in range(4) if q not in X) + u2
                    ov = len(I - cupX) + sum(z[q] for q in range(4) if q not in X) + zU
                    if ux + f1 + f2 - ov < 61: ok = False; break
            for (BA, oA, BB, oB) in ((B1, o1, B2, o2), (B2, o2, B1, o1)):
                if not ok: break
                for k in range(4):
                    if len(BA & PB[k]) + oA[k] != 5: continue
                    inside = (BA & PB[k]) <= BB and z[k] == oA[k]
                    if inside: continue
                    val = len(BB & PB[k]) + oB[k] + len(I - PB[k]) + sum(z[q] for q in range(4) if q != k) + zU
                    if val > 9: ok = False; break
            if ok: return True
    return False
if __name__ == '__main__':
    ST = {b: s for b, s in json.load(open('w14_states.json'))}
    T = np.load('w14_conf.npz')['T']
    pairs = np.load(sys.argv[1]); k = int(sys.argv[2]); random.seed(int(sys.argv[3]))
    idx = random.sample(range(len(pairs)), min(k, len(pairs)))
    bad = 0
    for r in idx:
        i, j = map(int, pairs[r]); bi, bj = int(T[i]), int(T[j])
        if any(feasible_pair(bi, oi, bj, oj) for oi in ST[bi] for oj in ST[bj]):
            bad += 1; print('DISAGREE', i, j, bi, bj)
    print('checked', len(idx), 'conflict pairs; disagreements', bad)
