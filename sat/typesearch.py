"""Structured (orbit-closed) search for Erdos #616 constructions.
X = A_1 u ... u A_p (|A_j| = alpha_j). A 'type' is a vector a=(a_1..a_p), 0<=a_j<=alpha_j;
family F = all T subset X with |T cap A_j| = a_j for some chosen type, each with K copies
(edge = S u privates, S = X \\ T, needs |S| <= r-1).  tau >= K  <=> every (K-1)-subset of X lies in some T.
Local property L_r fails iff some multiset of chosen types admits a covering configuration (union T = X) with
span = (n - d) + sum (r - |S_i|) <= 3r-3, where d = sum_j dmax_j,
dmax_j = max{ d <= min_i a_ij : sum_i a_ij - alpha_j >= (m-1) d }  (requires sum_i a_ij >= alpha_j).
Usage: python typesearch.py r K alpha_1 [alpha_2 ...]"""
import sys, itertools
from pysat.solvers import Solver

def run(r, K, alphas, verbose=True):
    p = len(alphas); n = sum(alphas); lim = 3 * r - 3
    types = [a for a in itertools.product(*[range(al + 1) for al in alphas])
             if sum(a) >= K - 1 and n - sum(a) <= r - 1 and n - sum(a) >= 1]
    idx = {a: i + 1 for i, a in enumerate(types)}
    s_of = {a: n - sum(a) for a in types}
    clauses = []
    for c in itertools.product(*[range(al + 1) for al in alphas]):
        if sum(c) != K - 1: continue
        lits = [idx[a] for a in types if all(a[j] >= c[j] for j in range(p))]
        if not lits:
            return 'UNSAT-P1', None
        clauses.append(lits)
    bad = set()
    def minspan(ms):
        return sum(r - s_of[a] for a in ms) + sum(max(alphas[j] - a[j] for a in ms) for j in range(p))
    def violating(ms):
        m = len(ms); d = 0
        for j in range(p):
            col = [a[j] for a in ms]
            tot = sum(col) - alphas[j]
            if tot < 0: return False
            dj = min(min(col), tot // (m - 1)) if m > 1 else min(col)
            d += dj
        span = (n - d) + sum(r - s_of[a] for a in ms)
        return span <= lim
    nodes = 0
    def dfs(ms, start):
        nonlocal nodes
        nodes += 1
        if len(ms) >= 1 and violating(ms):
            bad.add(frozenset(ms)); return
        for i in range(start, len(types)):
            ms2 = ms + [types[i]]
            if minspan(ms2) > lim: continue
            dfs(ms2, i)
    dfs([], 0)
    badl = sorted(bad, key=len)
    mins = []
    for b in badl:
        if not any(m <= b for m in mins):
            mins.append(b)
    for b in mins:
        clauses.append([-idx[a] for a in b])
    with Solver(name='cadical153', bootstrap_with=clauses) as s:
        res = s.solve()
        if verbose:
            print(f'r={r} K={K} alphas={alphas} types={len(types)} nodes={nodes} badsets={len(mins)} ->', 'SAT' if res else 'UNSAT', flush=True)
        if res:
            m = s.get_model()
            chosen = [types[v - 1] for v in m if v > 0 and v <= len(types)]
            return 'SAT', chosen
    return 'UNSAT', None

if __name__ == '__main__':
    r, K = int(sys.argv[1]), int(sys.argv[2])
    alphas = list(map(int, sys.argv[3:]))
    print(run(r, K, alphas))
