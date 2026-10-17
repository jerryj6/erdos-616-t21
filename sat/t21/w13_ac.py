"""Wave 13: pairwise arc consistency over the 24 first-generation single domains (w13_dom.json).
Each state = (core trace b, o-vector). Two states of different single types are INCOMPATIBLE only if a proved lemma
fails for every possible realization of their O/U overlaps (sound: overlaps are bracketed by [lo, hi]).
Rules: Lemma A; F1 with each base edge; same base pair & different type: S(a) (outside P_i u P_j disjoint, incl. O_k, U),
NT (W7-I: a,c >= 2, never 1), a+c>=5; OO = L on {P_k,P_l,F,F'} (F&F'&N_kl = {}); L on {P_k,P_l,P_m,F,F'} (F&F'&T = {});
D1 at derived 5-pairs (P_k,F) whenever |F&P_k| = 5 and N' = F&P_k is surely not inside F'.
"""
import json, itertools, sys, numpy as np
from w13_enum import *
D = json.load(open('w13_dom.json'))
keys = list(D)
typ = {k: (int(k[1]), int(k[3])) for k in keys}
Pm = np.array(P, dtype=np.int64); OS = np.array(OSZ)
PC = np.array([bin(x).count('1') for x in range(1 << n)], dtype=np.int64)
arr = {}
for k in keys:
    b = np.array([s[0] for s in D[k]], dtype=np.int64); o = np.array([s[1] for s in D[k]], dtype=np.int64)
    u = 21 - PC[b] - o.sum(1)
    arr[k] = (b, o, u)
NKL = {kl: P[kl[0]] & P[kl[1]] for kl in PAIRS}

def compat(k1, k2):
    b1, o1, u1 = arr[k1]; b2, o2, u2 = arr[k2]
    B1 = b1[:, None]; B2 = b2[None, :]
    O1 = o1[:, None, :]; O2 = o2[None, :, :]
    U1 = u1[:, None]; U2 = u2[None, :]
    i1, j1 = typ[k1]; i2, j2 = typ[k2]
    same = (i1, j1) == (i2, j2)
    I = B1 & B2
    ovhi = np.minimum(O1, O2)                       # upper bound of |F&F'&O_k|
    ovlo = np.maximum(0, O1 + O2 - OS[None, None, :])  # forced overlap (pigeonhole)
    uhi = np.minimum(U1, U2)
    ok = np.ones(I.shape, bool)
    if same:
        for q in range(4):
            if q in (i1, j1): continue
            ok &= ovlo[:, :, q] == 0
            ovhi[:, :, q] = 0
        uhi = np.zeros_like(uhi)
        Nij = NKL[(i1, j1)]
        ok &= (I & ~(P[i1] | P[j1]) & ((1 << n) - 1)) == 0       # S(a) named
        a_lo = PC[I & P[i1] & ~Nij & ((1<<n)-1)]; a_hi = a_lo + ovhi[:, :, i1]
        c_lo = PC[I & P[j1] & ~Nij & ((1<<n)-1)]; c_hi = c_lo + ovhi[:, :, j1]
        # need some a in [a_lo,a_hi] with a>=2 ; same for c ; and a_hi + c_hi >= 5
        ok &= (a_hi >= 2) & (c_hi >= 2) & (a_hi + c_hi >= 5)
    maxI = PC[I] + ovhi.sum(2) + uhi
    ok &= maxI >= 5
    for q in range(4):
        ok &= (PC[I & P[q]] > 0) | (ovhi[:, :, q] >= 1)
    # OO on base pairs
    for (k, l), Nkl in NKL.items():
        m = (I & Nkl) == 0
        out = ~(P[k] | P[l]) & ((1 << n) - 1)
        s1 = 9 - (PC[B1 & (P[k] | P[l])] + O1[:, :, k] + O1[:, :, l])
        s2 = 9 - (PC[B2 & (P[k] | P[l])] + O2[:, :, k] + O2[:, :, l])
        lo = PC[I & out] + sum(ovlo[:, :, q] for q in range(4) if q not in (k, l))
        ok &= ~m | (lo <= s1 + s2)
    # L on three base edges + F + F'
    for T, t in TRI.items():
        m = (I & t) == 0
        nn = [q for q in range(4) if q not in T][0]
        U3 = P[T[0]] | P[T[1]] | P[T[2]]
        f1 = PC[B1 & U3] + sum(O1[:, :, q] for q in T); f2 = PC[B2 & U3] + sum(O2[:, :, q] for q in T)
        lo = ovlo[:, :, nn]
        ok &= ~m | (lo <= 29 + PC[t] - f1 - f2)
    # D1 at derived pairs (P_k, F) and (P_k, F')
    for (BA, OA, BB, OB, swap) in ((B1, O1, B2, O2, False), (B2, O2, B1, O1, True)):
        for k in range(4):
            five = (PC[BA & P[k]] + OA[:, :, k]) == 5
            notin = ((BA & P[k] & ~BB) != 0) | (OA[:, :, k] > OB[:, :, k])
            # |F'&(P_k u F)| >= |F'&P_k| + lo|F&F' \ P_k|
            lo = PC[I & ~P[k] & ((1<<n)-1)] + sum(ovlo[:, :, q] for q in range(4) if q != k)
            val = PC[BB & P[k]] + OB[:, :, k] + lo
            ok &= ~(five & notin) | (val <= 9)
    return ok

if __name__ == '__main__':
    alive = {k: np.ones(len(D[k]), bool) for k in keys}
    C = {}
    for k1, k2 in itertools.combinations(keys, 2):
        C[(k1, k2)] = compat(k1, k2)
    print('pairs built', flush=True)
    changed = True; it = 0
    while changed:
        changed = False; it += 1
        for k1, k2 in itertools.combinations(keys, 2):
            M = C[(k1, k2)] & alive[k1][:, None] & alive[k2][None, :]
            s1 = M.any(1); s2 = M.any(0)
            if (alive[k1] & ~s1).any(): alive[k1] &= s1; changed = True
            if (alive[k2] & ~s2).any(): alive[k2] &= s2; changed = True
        print('iter', it, {k: int(alive[k].sum()) for k in keys}, flush=True)
    json.dump({k: [D[k][i] for i in np.nonzero(alive[k])[0]] for k in keys}, open('w13_dom_ac.json', 'w'))
    for k in keys:
        st = [D[k][i] for i in np.nonzero(alive[k])[0]]
        AND = (1 << n) - 1; OR = 0
        for b, o in st: AND &= b; OR |= b
        print(f'{k:12s} states {len(D[k]):4d} -> {len(st):4d}  traces {len(set(b for b,o in st)):4d}  forced-in {nm(AND)}  never {nm(((1<<n)-1) & ~OR)}')
