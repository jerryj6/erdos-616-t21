"""Wave 14: SOUND pairwise compatibility of two new-edge states s1=(b1,o1), s2=(b2,o2) (distinct edges F,F').
Unknowns: z_q = |F&F'&O_q| in [zlo_q, zhi_q], zu = |F&F'&U| in [0, min(u1,u2)], u = 21-|b|-sum o.
A state pair is declared INCOMPATIBLE only if one of the following PROVED necessary conditions fails for every
admissible z (each test uses only lower bounds of quantities that must be <= and upper bounds of those that must be >=):
 SAME  cross-type singles of one base pair (i,j) (|b1&N|=|b2&N|=1, different points): S(a) no common point outside
       P_i u P_j (core, O_q q!=i,j, U); NT (W7-I) a=|F&F'&(P_i\\N)|>=2, c>=2; S(b) a+c>=5.
 A     Lemma A: |F&F'| >= 5.
 F1    {P_q,F,F'} has a common point: b1&b2&P_q != {} or z_q >= 1.
 OO    L on {P_k,P_l,F,F'} when b1&b2&N_kl = {}: |(F&F') \\ (P_k u P_l)| <= s1+s2, s = 9-|F&(P_k u P_l)|.
 L3'   L on {P_i,P_j,P_k,F,F'} when b1&b2&T_ijk = {}: |(F&F')\\U3| <= 29+|T|-f1-f2.
 D1d   D1 at derived 5-pair (P_k,F) (|F&P_k|=5) when N'=F&P_k surely not inside F': |F'&(P_k u F)| <= 9 (both orders).
Lower bound on overlaps outside a set X of base edges uses max(sum of forced parts, 5 - max overlap inside X) (Lemma A)."""
import sys, itertools, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, OSZ, n, N, TRI, PAIRS
MASK = (1 << n) - 1
PC = np.array([bin(x).count('1') for x in range(1 << n)], dtype=np.int64)
OS = np.array(OSZ, dtype=np.int64)
NKL = {kl: P[kl[0]] & P[kl[1]] for kl in PAIRS}

def compat(b1, o1, b2, o2, drop=()):
    """b: int arrays, o: (len,4) arrays. returns bool matrix (len1, len2): True = possibly compatible."""
    u1 = 21 - PC[b1] - o1.sum(1); u2 = 21 - PC[b2] - o2.sum(1)
    B1 = b1[:, None]; B2 = b2[None, :]
    O1 = o1[:, None, :]; O2 = o2[None, :, :]
    I = B1 & B2
    zhi = np.minimum(O1, O2).copy()
    zlo = np.maximum(0, O1 + O2 - OS[None, None, :])
    uhi = np.minimum(u1[:, None], u2[None, :]).copy()
    ok = np.ones(I.shape, bool)
    for (i, j), Nij in (NKL.items() if 'SAME' not in drop else []):
        s1 = B1 & Nij; s2 = B2 & Nij
        same = (PC[s1] == 1) & (PC[s2] == 1) & (s1 != s2)
        if not same.any(): continue
        out = MASK & ~(P[i] | P[j])
        bad = (I & out) != 0
        for q in range(4):
            if q in (i, j): continue
            bad |= same & (zlo[:, :, q] > 0)
            zhi[:, :, q] = np.where(same, 0, zhi[:, :, q])
        uhi = np.where(same, 0, uhi)
        a_hi = PC[I & P[i] & ~Nij & MASK] + zhi[:, :, i]
        c_hi = PC[I & P[j] & ~Nij & MASK] + zhi[:, :, j]
        bad |= (a_hi < 2) | (c_hi < 2) | (a_hi + c_hi < 5)
        ok &= ~(same & bad)
    # F1 with each base edge; forced z
    for q in range(4):
        need = (PC[I & P[q]] == 0)
        if 'F1' in drop: continue
        ok &= ~need | (zhi[:, :, q] >= 1)
        zlo[:, :, q] = np.maximum(zlo[:, :, q], need.astype(np.int64))
    if 'A' not in drop: ok &= (PC[I] + zhi.sum(2) + uhi) >= 5
    def outlo(X):  # lower bound of |F&F' outside union of base edges in X|
        Xm = 0
        for q in X: Xm |= P[q]
        f = PC[I & ~Xm & MASK] + sum(zlo[:, :, q] for q in range(4) if q not in X)
        inside_hi = PC[I & Xm] + sum(zhi[:, :, q] for q in X)
        return f if 'A' in drop else np.maximum(f, 5 - inside_hi)
    for (k, l), Nkl in (NKL.items() if 'OO' not in drop else []):
        m = (I & Nkl) == 0
        s1 = 9 - (PC[B1 & (P[k] | P[l])] + O1[:, :, k] + O1[:, :, l])
        s2 = 9 - (PC[B2 & (P[k] | P[l])] + O2[:, :, k] + O2[:, :, l])
        ok &= ~m | (outlo((k, l)) <= s1 + s2)
    for T, t in (TRI.items() if 'L3' not in drop else []):
        m = (I & t) == 0
        U3 = P[T[0]] | P[T[1]] | P[T[2]]
        f1 = PC[B1 & U3] + sum(O1[:, :, q] for q in T); f2 = PC[B2 & U3] + sum(O2[:, :, q] for q in T)
        ok &= ~m | (outlo(T) <= 29 + PC[t] - f1 - f2)
    for (BA, OA, BB, OB) in ((B1, O1, B2, O2), (B2, O2, B1, O1)):
        for k in (range(4) if 'D1d' not in drop else []):
            five = (PC[BA & P[k]] + OA[:, :, k]) == 5
            notin = ((BA & P[k] & ~BB) != 0) | (OA[:, :, k] > OB[:, :, k])
            val = PC[BB & P[k]] + OB[:, :, k] + outlo((k,))
            ok &= ~(five & notin) | (val <= 9)
    return ok
