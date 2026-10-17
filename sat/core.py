"""Erdos #616 core reformulation.
A hypergraph = family of 'core parts' S_i subset X plus private vertices (r-|S_i| each).
Local property L_r: every subfamily with empty intersection of S's has span
   |U S_i| + sum (r-|S_i|) >= 3r-2.
tau >= k  (with free multiplicity, |S_i|<=r-1) iff every (k-1)-subset of X is disjoint from some S_i.
"""
import numpy as np
from numba import njit

@njit(cache=True)
def popc(x):
    c = 0
    while x:
        x &= x - 1
        c += 1
    return c

@njit(cache=True)
def find_violations(S, r, maxdepth, cap):
    """S: int64 array of core masks. Return list of violating subfamilies (index tuples padded with -1):
    subfamilies (size>=2) with empty intersection and span <= 3r-3. DFS with span pruning (span is monotone)."""
    N = S.shape[0]
    lim = 3 * r - 3
    out = np.full((cap, maxdepth), -1, np.int64)
    cnt = 0
    w = np.empty(N, np.int64)
    for i in range(N):
        w[i] = r - popc(S[i])
    wmin = w.min() if N > 0 else 0
    idx = np.empty(maxdepth, np.int64)
    inter = np.empty(maxdepth, np.int64)
    uni = np.empty(maxdepth, np.int64)
    ws = np.empty(maxdepth, np.int64)
    # iterative DFS
    depth = 0
    idx[0] = -1
    while depth >= 0:
        idx[depth] += 1
        if idx[depth] >= N:
            depth -= 1
            continue
        j = idx[depth]
        if depth == 0:
            inter[0] = S[j]; uni[0] = S[j]; ws[0] = w[j]
        else:
            inter[depth] = inter[depth-1] & S[j]
            uni[depth] = uni[depth-1] | S[j]
            ws[depth] = ws[depth-1] + w[j]
        span = popc(uni[depth]) + ws[depth]
        if span > lim:
            continue
        if inter[depth] == 0:
            if cnt < cap:
                for t in range(depth+1):
                    out[cnt, t] = idx[t]
            cnt += 1
            continue
        if depth + 1 < maxdepth and span + wmin <= lim:
            depth += 1
            idx[depth] = j
    return out[:min(cnt, cap)], cnt

def tau_lower_ok(S, n, k):
    """every (k-1)-subset of [n] disjoint from some S."""
    from itertools import combinations
    Sarr = list(S)
    for C in combinations(range(n), k-1):
        cm = sum(1 << v for v in C)
        if not any((s & cm) == 0 for s in Sarr):
            return False, C
    return True, None

def exact_tau(S, r, cap=10):
    """exact tau of hypergraph with core parts S (each with r-|S| privates, multiplicity 1).
    tau = min_C |C| + #{i: S_i & C == 0}, over C subset of X; brute force over small C."""
    from itertools import combinations
    X = 0
    for s in S: X |= s
    verts = [v for v in range(64) if X >> v & 1]
    best = len(S)
    for h in range(0, cap+1):
        if h >= best: break
        for C in combinations(verts, h):
            cm = sum(1 << v for v in C)
            miss = sum(1 for s in S if (s & cm) == 0)
            if miss and any(popc(s) == r for s in S if (s & cm) == 0):
                # edge with no private: must be covered by a core vertex; count as >= 1 anyway (lower bound ok)
                pass
            best = min(best, h + miss)
    return best
