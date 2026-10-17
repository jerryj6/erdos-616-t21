"""REFEREE (independent) pairwise conflict checker (numba port of pairref.c; no shared code with w14_*).
Rules (literal statements; a pair of distinct non-base edges is COMPATIBLE if SOME state pair and SOME integer overlap
vector z_q=|F&F'&O_q| in [max(0,o+o'-|O_q|), min(o,o')], zU=|F&F'&U| in [0, min(u,u')] satisfies ALL):
  A    |F&F'| >= 5
  F1   F&F'&P_q nonempty for each q
  SAME singles of one base pair (i,j) of different types: no common point outside P_i u P_j; a,c >= 2; a+c >= 5
  L    every set X of >=2 base edges with (cap X)&F&F' empty: |U X u F u F'| >= 61 (exact)
  D1   (P_k,F) 5-pair (|F&P_k|=5) with F&P_k not inside F': |F'&(P_k u F)| <= 9, both orders.
usage: python3 pairref.py STATES.npz CNF [maxclauses]   (STATES from ref_universe.py: arrays var,b,o (var = CNF variable))
Prints counts and every binary clause that is NOT a conflict."""
import sys, numpy as np, numba as nb
from ref_states import Pm, OSZ
P = np.array(Pm, np.int64); OS = np.array(OSZ, np.int64)

@nb.njit(cache=True)
def pc(x):
    c = 0
    while x:
        x &= x - 1; c += 1
    return c

@nb.njit(cache=True)
def feasible(b1, o1, b2, o2, P, OS, drop=0):
    # drop bits: 1=A 2=F1 4=SAME 8=L(|X|=2,OO) 16=L(|X|=3) 32=L(|X|=4) 64=D1(derived)
    I = b1 & b2
    u1 = 21 - pc(b1) - o1[0] - o1[1] - o1[2] - o1[3]
    u2 = 21 - pc(b2) - o2[0] - o2[1] - o2[2] - o2[3]
    lo = np.zeros(4, np.int64); hi = np.zeros(4, np.int64)
    for q in range(4):
        lo[q] = max(0, o1[q] + o2[q] - OS[q]); hi[q] = min(o1[q], o2[q])
        if lo[q] > hi[q]: return False
    uh = min(u1, u2)
    si = np.zeros(6, np.int64); sj = np.zeros(6, np.int64); ns = 0
    for i in range(4):
        for j in range(i + 1, 4):
            N = P[i] & P[j]; x = b1 & N; y = b2 & N
            if pc(x) == 1 and pc(y) == 1 and x != y:
                si[ns] = i; sj[ns] = j; ns += 1
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
                        ok = True
                        if not (drop & 1) and pc(I) + z0 + z1 + z2 + z3 + zu < 5: ok = False
                        for q in range(4):
                            if ok and not (drop & 2) and (I & P[q]) == 0 and z[q] == 0: ok = False
                        for t in range(ns):
                            if not ok or (drop & 4): break
                            i = si[t]; j = sj[t]
                            if I & ~(P[i] | P[j]) & 0xffff: ok = False
                            for q in range(4):
                                if q != i and q != j and z[q] > 0: ok = False
                            if zu > 0: ok = False
                            a = pc(I & P[i] & ~P[j]) + z[i]; c = pc(I & P[j] & ~P[i]) + z[j]
                            if a < 2 or c < 2 or a + c < 5: ok = False
                        for X in range(1, 16):
                            if not ok: break
                            if pc(X) < 2: continue
                            if (drop >> (pc(X) + 1)) & 1: continue
                            cap = 0xffff; cup = 0; ux = 0
                            for q in range(4):
                                if (X >> q) & 1:
                                    cap &= P[q]; cup |= P[q]; ux += OS[q]
                            if cap & I: continue
                            ux += pc(cup)
                            f1 = pc(b1 & ~cup & 0xffff) + u1; f2 = pc(b2 & ~cup & 0xffff) + u2; ov = pc(I & ~cup & 0xffff) + zu
                            for q in range(4):
                                if not ((X >> q) & 1):
                                    f1 += o1[q]; f2 += o2[q]; ov += z[q]
                            if ux + f1 + f2 - ov < 61: ok = False
                        for sw in range(2):
                            if not ok or (drop & 64): break
                            if sw == 0:
                                bA = b1; oA = o1; bB = b2; oB = o2
                            else:
                                bA = b2; oA = o2; bB = b1; oB = o1
                            for k in range(4):
                                if not ok: break
                                if pc(bA & P[k]) + oA[k] != 5: continue
                                if (bA & P[k] & ~bB) == 0 and z[k] == oA[k]: continue
                                val = pc(bB & P[k]) + oB[k] + pc(I & ~P[k] & 0xffff) + zu
                                for q in range(4):
                                    if q != k: val += z[q]
                                if val > 9: ok = False
                        if ok: return True
    return False

@nb.njit(cache=True)
def check_pairs(pa, pb, first, cnt, B, O, P, OS, drop=0):
    res = np.zeros(len(pa), np.int8)   # 1 = compatible (disagreement), 2 = vacuous (a var without states)
    for r in range(len(pa)):
        a = pa[r]; c = pb[r]
        if cnt[a] == 0 or cnt[c] == 0:
            res[r] = 2; continue
        comp = False
        for i in range(first[a], first[a] + cnt[a]):
            for j in range(first[c], first[c] + cnt[c]):
                if feasible(B[i], O[i], B[j], O[j], P, OS, drop):
                    comp = True; break
            if comp: break
        if comp: res[r] = 1
    return res

def load_states(path):
    d = np.load(path); var = d['var']; B = d['b']; O = d['o']
    NV = int(var.max()) + 2
    first = np.zeros(NV, np.int64); cnt = np.zeros(NV, np.int64)
    for i, v in enumerate(var.tolist()):
        if cnt[v] == 0: first[v] = i
        cnt[v] += 1
    assert np.all(np.diff(var) >= 0)
    return first, cnt, B, O

def read_binary(cnf):
    pa = []; pb = []; other = []
    with open(cnf) as fh:
        for line in fh:
            if line[0] in 'pc': continue
            l = line.split()
            if len(l) == 3 and l[0][0] == '-' and l[1][0] == '-':
                pa.append(-int(l[0])); pb.append(-int(l[1]))
            else:
                other.append([int(x) for x in l[:-1]])
    return np.array(pa, np.int64), np.array(pb, np.int64), other

if __name__ == '__main__':
    first, cnt, B, O = load_states(sys.argv[1])
    pa, pb, other = read_binary(sys.argv[2])
    if len(sys.argv) > 3:
        m = int(sys.argv[3]); pa = pa[:m]; pb = pb[:m]
    print('binary clauses', len(pa), 'other clauses', len(other), 'self-pairs', int((pa == pb).sum()), flush=True)
    res = check_pairs(pa, pb, first, cnt, B, O, P, OS)
    bad = np.nonzero(res == 1)[0]; vac = int((res == 2).sum())
    for r in bad[:50]: print('DISAGREE', pa[r], pb[r])
    print('checked', len(pa), 'disagreements', len(bad), 'vacuous', vac, flush=True)
