"""REFEREE (independent, W11 §5): trace-level relaxation of the N-noK4 base configuration of class (a,c).
Written from the lemma statements only; imports nothing from w9/w10x/w11/w13/w14 (nor from w14ref).

Base (forced by R.3 + S(a), W11.1 / referee §1): E1=P0, E2=P1, G=P2 (single of type v at (E1,E2)), H=P3 (type w),
|A_G∩A_H| = a (al*), |C_G∩C_H| = c (cl*). CORE = points in >= 2 base edges:
  v{0,1,2} w{0,1,3} m0..m2{0,1} al*{0,2,3} ag*{0,2} ah*{0,3} cl*{1,2,3} cg*{1,2} ch*{1,3}   (21-a-c points)
private parts O_q (points in exactly one base edge): |O_0| = 8+a, |O_1| = 8+c, |O_2| = |O_3| = 12.  Total 61.
A non-base edge X has a STATE (b, o0..o3): b = X∩CORE (bitmask), o_q = |X∩O_q|, u = 21-|b|-Σo >= 0 points outside.

Lemma statements used (each proved for ANY edges of an N-noK4 counterexample, refereed SOUND earlier):
  A    two distinct edges meet in >= 5 points
  F1   three edges have a common point
  L    a subfamily with no common point has union >= 61
  D1   (X,Y) 5-pair, N = X∩Y, L an edge with N ⊄ L  =>  |L∩(X∪Y)| <= 9
  R3   (X,Y) 5-pair, Z single (|Z∩N| = 1)  =>  |Z∩X| = |Z∩Y| = 5
  SA   (X,Y) 5-pair, Z1,Z2 singles of different types => Z1∩Z2 ⊆ X∪Y          (R.3 / S(a))
  CLS  same hypothesis, a = |Z1∩Z2∩(X∖Y)|, c = |Z1∩Z2∩(Y∖X)|:
         W7-I: a,c >= 2;  NK (N-noK4 + N.0): a+c >= 6;  N24 (Wave 10, refereed): (a,c) ∉ {(2,4),(4,2)}
         optional flag N34 (W11 (3,4) closure, refereed §3a): (a,c) ∉ {(3,4),(4,3)}   [OFF unless stated]
"""
import itertools, numpy as np, numba as nb

def base(a, c):
    names = ['v', 'w', 'm0', 'm1', 'm2'] + [f'al{i}' for i in range(a)] + [f'ag{i}' for i in range(4 - a)] + \
            [f'ah{i}' for i in range(4 - a)] + [f'cl{i}' for i in range(c)] + [f'cg{i}' for i in range(4 - c)] + \
            [f'ch{i}' for i in range(4 - c)]
    REG = {'v': (0, 1, 2), 'w': (0, 1, 3), 'm': (0, 1), 'al': (0, 2, 3), 'ag': (0, 2), 'ah': (0, 3),
           'cl': (1, 2, 3), 'cg': (1, 2), 'ch': (1, 3)}
    reg = lambda nm: nm.rstrip('0123456789')
    n = len(names); assert n == 21 - a - c
    Pm = [sum(1 << x for x in range(n) if q in REG[reg(names[x])]) for q in range(4)]
    OS = [21 - bin(Pm[q]).count('1') for q in range(4)]
    assert OS == [8 + a, 8 + c, 12, 12], OS
    pc = lambda x: bin(x).count('1')
    # sanity: the defining relations of the class
    assert pc(Pm[0] & Pm[1]) == 5 and pc(Pm[0] & Pm[2]) == 5 and pc(Pm[0] & Pm[3]) == 5
    assert pc(Pm[1] & Pm[2]) == 5 and pc(Pm[1] & Pm[3]) == 5 and pc(Pm[2] & Pm[3]) == a + c
    M = Pm[0] & Pm[1]
    assert Pm[2] & M == 1 and Pm[3] & M == 2                          # G type v, H type w
    assert pc(Pm[2] & Pm[3] & Pm[0] & ~M) == a and pc(Pm[2] & Pm[3] & Pm[1] & ~M) == c
    assert sum(OS) + n == 61 and (Pm[0] & Pm[1] & Pm[2] & Pm[3]) == 0
    return names, np.array(Pm, np.int64), np.array(OS, np.int64)

@nb.njit(cache=True)
def pc(x):
    c = 0
    while x:
        x &= x - 1; c += 1
    return c

@nb.njit(cache=True)
def cls_ok(a, c, n34):
    if not (n34 & 8) and (a < 2 or c < 2): return False          # W7-I (off with flag 8: control only)
    if not (n34 & 4) and a + c < 6: return False                 # NK   (off with flag 4: control only)
    if a < 1 or c < 1 or a + c < 5: return False                 # S(a)/S(b) (kept in every run)
    if not (n34 & 2) and ((a == 2 and c == 4) or (a == 4 and c == 2)): return False   # N24 (off with flag bit 2: '(2,4)' run)
    if (n34 & 1) and ((a == 3 and c == 4) or (a == 4 and c == 3)): return False       # N34 (flag bit 1)
    return True

@nb.njit(cache=True)
def edge_ok(b, o, P, OS, FULL, n34):
    """per-edge rules for one non-base edge with state (b,o)."""
    s = pc(b)
    for q in range(4):
        if o[q] < 0 or o[q] > OS[q]: return False
        s += o[q]
    if s > 21: return False
    u = 21 - s
    x = np.zeros(4, np.int64)
    for q in range(4):
        x[q] = pc(b & P[q]) + o[q]
        if x[q] < 5: return False                                   # A
    for i in range(4):
        for j in range(i + 1, 4):
            if (b & P[i] & P[j]) == 0: return False                 # F1 with {P_i,P_j,X}
    # L on {S, X}, S = set of >= 2 base edges (|S|=2 is F1; |S|=4 vacuous; kept generic)
    for S in range(1, 16):
        if pc(S) < 2: continue
        cap = FULL; cup = 0; us = 0
        for q in range(4):
            if (S >> q) & 1:
                cap &= P[q]; cup |= P[q]; us += OS[q]
        if b & cap: continue
        us += pc(cup)
        out = pc(b & ~cup & FULL) + u
        for q in range(4):
            if not ((S >> q) & 1): out += o[q]
        if us + out < 61: return False
    # base 5-pairs
    for i in range(4):
        for j in range(i + 1, 4):
            N = P[i] & P[j]
            if pc(N) != 5: continue
            bn = b & N
            if bn != N and x[i] + x[j] - pc(bn) > 9: return False    # D1 at a base pair
            if pc(bn) == 1:
                if x[i] != 5 or x[j] != 5: return False              # R3
                for k in range(4):
                    if k == i or k == j: continue
                    y = P[k] & N
                    if pc(y) != 1 or y == bn: continue               # P_k base single of another type
                    if (b & P[k] & ~(P[i] | P[j])) != 0 or o[k] != 0: return False   # SA
                    a_ = pc(b & P[k] & P[i] & ~P[j]); c_ = pc(b & P[k] & P[j] & ~P[i])
                    if not cls_ok(a_, c_, n34): return False
    # derived 5-pairs (P_i, X): N = (b & P_i) + o_i points of O_i
    for i in range(4):
        if x[i] != 5: continue
        Nc = b & P[i]
        for j in range(4):
            if j == i: continue
            inside = (o[i] == 0) and ((Nc & ~P[j]) == 0)
            if not inside and pc(P[j] & P[i]) + pc(b & P[j] & ~P[i]) + o[j] > 9: return False   # D1
            if pc(P[j] & Nc) == 1 and x[j] != 5: return False                                    # R3
        for j in range(4):
            if j == i or pc(P[j] & Nc) != 1: continue
            for k in range(j + 1, 4):
                if k == i or pc(P[k] & Nc) != 1: continue
                if (P[j] & P[k] & Nc) != 0: continue                 # same type
                Pjk = P[j] & P[k]
                if (Pjk & ~P[i] & ~b) != 0: return False             # SA: P_j∩P_k ⊆ P_i ∪ X (core only)
                a_ = pc(Pjk & P[i] & ~b); c_ = pc(Pjk & b & ~P[i])
                if not cls_ok(a_, c_, n34): return False
    return True

@nb.njit(cache=True)
def edge_states(b, P, OS, FULL, n34, out):
    """fill out[k] with every o admissible for trace b; returns count. Box: L_q..min(OS_q, 21-|b|-ΣL)"""
    s = pc(b); L = np.zeros(4, np.int64)
    for q in range(4):
        L[q] = max(0, 5 - pc(b & P[q]))
    rem = 21 - s - L[0] - L[1] - L[2] - L[3]
    if rem < 0: return 0
    k = 0; o = np.zeros(4, np.int64)
    for o0 in range(L[0], min(OS[0], L[0] + rem) + 1):
        for o1 in range(L[1], min(OS[1], L[1] + rem - (o0 - L[0])) + 1):
            for o2 in range(L[2], min(OS[2], L[2] + rem - (o0 - L[0]) - (o1 - L[1])) + 1):
                for o3 in range(L[3], min(OS[3], L[3] + rem - (o0 - L[0]) - (o1 - L[1]) - (o2 - L[2])) + 1):
                    o[0] = o0; o[1] = o1; o[2] = o2; o[3] = o3
                    if edge_ok(b, o, P, OS, FULL, n34):
                        out[k, 0] = o0; out[k, 1] = o1; out[k, 2] = o2; out[k, 3] = o3; k += 1
    return k

@nb.njit(cache=True)
def pair_ok(b1, o1, b2, o2, P, OS, FULL, n34, drop):
    """True iff two DISTINCT non-base edges with these states can coexist: some integer overlap vector
    z_q = |F1∩F2∩O_q| in [max(0,o1+o2-|O_q|), min(o1,o2)], zu = |F1∩F2 ∩ outside| in [0, min(u1,u2)] satisfies all rules.
    drop bits (controls): 1 A, 2 F1, 4 L, 8 SAME(base pair), 16 D1 derived (P_k,F), 32 single-rules at (P_k,F),
    64 rules at the derived 5-pair (F,F'), 128 CLS everywhere in pair rules (W7/NK/N24 kept as SA only)."""
    I = b1 & b2
    u1 = 21 - pc(b1) - o1[0] - o1[1] - o1[2] - o1[3]
    u2 = 21 - pc(b2) - o2[0] - o2[1] - o2[2] - o2[3]
    lo = np.zeros(4, np.int64); hi = np.zeros(4, np.int64)
    for q in range(4):
        lo[q] = max(0, o1[q] + o2[q] - OS[q]); hi[q] = min(o1[q], o2[q])
        if lo[q] > hi[q]: return False
    x1 = np.zeros(4, np.int64); x2 = np.zeros(4, np.int64)
    for q in range(4):
        x1[q] = pc(b1 & P[q]) + o1[q]; x2[q] = pc(b2 & P[q]) + o2[q]
    uh = min(u1, u2)
    z = np.zeros(4, np.int64)
    for z0 in range(lo[0], hi[0] + 1):
        z[0] = z0
        for z1 in range(lo[1], hi[1] + 1):
            z[1] = z1
            for z2 in range(lo[2], hi[2] + 1):
                z[2] = z2
                for z3 in range(lo[3], hi[3] + 1):
                    z[3] = z3
                    for zu in range(0, uh + 1):
                        if pair_rules(b1, o1, x1, u1, b2, o2, x2, u2, I, z, zu, P, OS, FULL, n34, drop):
                            return True
    return False

@nb.njit(cache=True)
def pair_rules(b1, o1, x1, u1, b2, o2, x2, u2, I, z, zu, P, OS, FULL, n34, drop):
    inter = pc(I) + z[0] + z[1] + z[2] + z[3] + zu
    if not (drop & 1) and inter < 5: return False                         # A
    if not (drop & 2):
        for q in range(4):
            if (I & P[q]) == 0 and z[q] == 0: return False                # F1 {P_q,F1,F2}
    if not (drop & 4):                                                    # L on {S, F1, F2}, |S| >= 2
        for S in range(1, 16):
            if pc(S) < 2: continue
            cap = FULL; cup = 0; us = 0
            for q in range(4):
                if (S >> q) & 1:
                    cap &= P[q]; cup |= P[q]; us += OS[q]
            if cap & I: continue
            us += pc(cup)
            f1 = pc(b1 & ~cup & FULL) + u1; f2 = pc(b2 & ~cup & FULL) + u2; ov = pc(I & ~cup & FULL) + zu
            for q in range(4):
                if not ((S >> q) & 1):
                    f1 += o1[q]; f2 += o2[q]; ov += z[q]
            if us + f1 + f2 - ov < 61: return False
    # SAME: both singles of a base 5-pair (i,j), different types
    if not (drop & 8):
        for i in range(4):
            for j in range(i + 1, 4):
                N = P[i] & P[j]
                if pc(N) != 5: continue
                s1 = b1 & N; s2 = b2 & N
                if pc(s1) != 1 or pc(s2) != 1 or s1 == s2: continue
                if (I & ~(P[i] | P[j]) & FULL) != 0 or zu != 0: return False       # SA
                for q in range(4):
                    if q != i and q != j and z[q] != 0: return False
                if not (drop & 128):
                    a_ = pc(I & P[i] & ~P[j]) + z[i]; c_ = pc(I & P[j] & ~P[i]) + z[j]
                    if not cls_ok(a_, c_, n34): return False
    # derived 5-pair (P_k, F), F in {1,2}, other edge F'
    for sw in range(2):
        if sw == 0:
            bA = b1; oA = o1; xA = x1; bB = b2; oB = o2; xB = x2
        else:
            bA = b2; oA = o2; xA = x2; bB = b1; oB = o1; xB = x1
        for k in range(4):
            if xA[k] != 5: continue
            # |F'∩F∖P_k|
            offk = pc(I & ~P[k] & FULL) + zu
            for q in range(4):
                if q != k: offk += z[q]
            nB = pc(I & P[k]) + z[k]                       # |F'∩N|
            if not (drop & 16):
                if nB < 5:                                 # N ⊄ F'
                    if xB[k] + offk > 9: return False      # D1
            if (drop & 32) or nB != 1: continue
            # F' single of (P_k, F)
            if xB[k] != 5 or nB + offk != 5: return False  # R3
            Nc = bA & P[k]
            for j in range(4):
                if j == k: continue
                y = Nc & P[j]
                if pc(y) != 1: continue                    # P_j single of (P_k,F)
                if (bB & y) != 0: continue                 # same type as F'
                if (bB & P[j] & ~P[k] & ~bA) != 0 or oB[j] - z[j] != 0: return False   # SA
                if not (drop & 128):
                    a_ = pc(bB & P[j] & P[k] & ~bA); c_ = pc(I & P[j] & ~P[k]) + z[j]
                    if not cls_ok(a_, c_, n34): return False
    # derived 5-pair (F1, F2)
    if not (drop & 64) and inter == 5:
        nj = np.zeros(4, np.int64)
        for j in range(4):
            nj[j] = pc(I & P[j]) + z[j]
            if nj[j] < 5 and x1[j] + x2[j] - nj[j] > 9: return False             # D1
            if nj[j] == 1 and (x1[j] != 5 or x2[j] != 5): return False           # R3
        for j in range(4):
            if nj[j] != 1: continue
            for k in range(j + 1, 4):
                if nj[k] != 1: continue
                Pjk = P[j] & P[k]
                if (I & Pjk) != 0: continue                                       # same type
                if (Pjk & ~(b1 | b2)) != 0: return False                          # SA
                if not (drop & 128):
                    if not cls_ok(pc(Pjk & b1 & ~b2), pc(Pjk & b2 & ~b1), n34): return False
    return True

@nb.njit(cache=True)
def trace_pair_compat(ia, ib, first, cnt, SB, SO, P, OS, FULL, n34, drop):
    for i in range(first[ia], first[ia] + cnt[ia]):
        for j in range(first[ib], first[ib] + cnt[ib]):
            if pair_ok(SB[i], SO[i], SB[j], SO[j], P, OS, FULL, n34, drop): return True
    return False

@nb.njit(cache=True)
def conf_rows(lo, hi, NT, first, cnt, SB, SO, P, OS, FULL, n34, drop):
    M = np.zeros((hi - lo, NT), np.uint8)
    for a in range(lo, hi):
        for c in range(a + 1, NT):
            if not trace_pair_compat(a, c, first, cnt, SB, SO, P, OS, FULL, n34, drop): M[a - lo, c] = 1
    return M
