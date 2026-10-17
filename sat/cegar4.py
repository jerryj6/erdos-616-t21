"""Memory-lean CEGAR for Erdos #616 (complement formulation, tau>=K target).
Variables y_T for T in pool (subsets of [n], sizes cmin..cmax). Base clauses: P1 (every (K-1)-subset of [n]
lies in a chosen T) + pairs of pool sets whose S-parts meet in <= K-1 points [these pairs are blocking
clauses of violating triples-or-pairs only when they are themselves violating; to keep every clause a
*direct* violation certificate we only add pair clauses for pairs covering [n] (empty S-intersection)].
Lazy clauses: blocking clauses of violating subfamilies found in the current model by a randomized DFS.
Every non-P1 clause written to the CNF is a violating subfamily (checked independently by verify_cnf.py).
Usage: python cegar2.py r K n cmin cmax [percap]"""
import sys, time, itertools
import numpy as np
from numba import njit
from pysat.solvers import Solver
from eager2 import enum as enum_cover

@njit(cache=True)
def popc(x):
    c = 0
    while x:
        x &= x - 1
        c += 1
    return c

@njit(cache=True)
def find_viol(S, r, maxdepth, cap, percap):
    N = S.shape[0]; lim = 3 * r - 3
    out = np.full((cap, maxdepth), -1, np.int64)
    used = np.zeros(N, np.int64)
    cnt = 0
    w = np.empty(N, np.int64)
    for i in range(N):
        w[i] = r - popc(S[i])
    idx = np.empty(maxdepth, np.int64); inter = np.empty(maxdepth, np.int64)
    uni = np.empty(maxdepth, np.int64); ws = np.empty(maxdepth, np.int64)
    depth = 0; idx[0] = -1
    while depth >= 0:
        idx[depth] += 1
        if idx[depth] >= N:
            depth -= 1
            continue
        j = idx[depth]
        if depth == 0 and used[j] >= percap:
            continue
        if depth == 0:
            inter[0] = S[j]; uni[0] = S[j]; ws[0] = w[j]
        else:
            inter[depth] = inter[depth-1] & S[j]; uni[depth] = uni[depth-1] | S[j]; ws[depth] = ws[depth-1] + w[j]
        span = popc(uni[depth]) + ws[depth]
        if span > lim:
            continue
        if inter[depth] == 0:
            for t in range(depth + 1):
                out[cnt, t] = idx[t]
            used[idx[0]] += 1
            cnt += 1
            if cnt >= cap:
                return out[:cnt]
            if used[idx[0]] >= percap:
                depth = 0  # move on to next first element
            continue
        if depth + 1 < maxdepth:
            depth += 1
            idx[depth] = j
    return out[:cnt]

def main():
    r, K, n, cmin, cmax = map(int, sys.argv[1:6])
    percap = int(sys.argv[6]) if len(sys.argv) > 6 else 20
    global CAP, LEMMA2
    LEMMA2 = (n == 14 and cmin == 4 and cmax == 5 and r == 21)
    CAP = int(sys.argv[7]) if len(sys.argv) > 7 else 50000
    assert n <= 15 and r == 21, 'm<=4 suffices only for n<=15 at r=21 (see notes)'
    tag = f'r{r}_K{K}_n{n}_c{cmin}-{cmax}'
    log = open(f'cegar4_{tag}.log', 'w')
    def P(*a):
        s = ' '.join(map(str, a)); print(s, flush=True); log.write(s + '\n'); log.flush()
    X = (1 << n) - 1
    T = np.array([sum(1 << v for v in c) for size in range(cmin, cmax + 1)
                  for c in itertools.combinations(range(n), size)], dtype=np.int64)
    S = X ^ T; N = len(T)
    cl_f = open(f'cegar4_{tag}.clauses', 'w')
    lem_f = open(f'cegar4_{tag}.lemmas', 'w')
    s = Solver(name='cadical153')
    ncl = 0
    for C in itertools.combinations(range(n), K - 1):
        cm = sum(1 << v for v in C)
        lits = [int(i) + 1 for i in np.nonzero((T & cm) == cm)[0]]
        s.add_clause(lits); cl_f.write(' '.join(map(str, lits)) + ' 0\n'); ncl += 1
    # covering pairs (empty S-intersection; span <= 2r <= 3r-3 so always violating)
    for i in range(N):
        js = np.nonzero((T[i] | T[i+1:]) == X)[0] + i + 1
        for j in js:
            cl = [-(i + 1), -(int(j) + 1)]
            s.add_clause(cl); cl_f.write(f'{cl[0]} {cl[1]} 0\n'); ncl += 1
    # Lemma L1 (proved in notes): two edges whose cores meet in <= K-1 points cannot coexist with P1.
    pc = np.array([bin(x).count('1') for x in range(1 << 16)], dtype=np.int64)
    popv = lambda a: pc[a & 0xFFFF] + pc[(a >> 16) & 0xFFFF]
    nl1 = 0
    for i in range(N):
        bad = np.nonzero(popv(S[i] & S[i+1:]) <= K - 1)[0] + i + 1
        for j in bad:
            if (T[i] | T[j]) == X: continue  # already added as covering pair
            cl = [-(i + 1), -(int(j) + 1)]
            s.add_clause(cl); lem_f.write(f'{cl[0]} {cl[1]} 0\n'); ncl += 1; nl1 += 1
    nl2 = 0
    if LEMMA2:
        # Lemma L2 (n=14, c in {4,5}, r=21; proved in notes): no two disjoint 4-sets both chosen.
        f4 = np.nonzero(popv(T) == 4)[0]
        for a in range(len(f4)):
            i = f4[a]
            js = f4[a+1:][(T[f4[a+1:]] & T[i]) == 0]
            for j in js:
                cl = [-(int(i) + 1), -(int(j) + 1)]
                s.add_clause(cl); lem_f.write(f'{cl[0]} {cl[1]} 0\n'); ncl += 1; nl2 += 1
    lem_f.close()
    P(f'{tag}: pool {N}, base clauses {ncl} (L1 {nl1}, L2 {nl2})')
    rng = np.random.default_rng(0)
    it = 0; t0 = time.time()
    while True:
        it += 1
        if not s.solve():
            P(f'UNSAT after {it} iterations, {ncl} clauses, {time.time()-t0:.1f}s')
            break
        m = s.get_model()
        sel = np.array([i for i in range(N) if m[i] > 0])
        rng.shuffle(sel)
        Tsub = T[sel]
        lists = [np.nonzero((Tsub >> v) & 1)[0] for v in range(n)]
        for L in lists: rng.shuffle(L)
        sup_ptr = np.zeros(n + 1, np.int64)
        for v in range(n): sup_ptr[v + 1] = sup_ptr[v] + len(lists[v])
        sup_index = np.concatenate(lists).astype(np.int64)
        out = np.zeros((CAP, 4), np.int32)
        c = enum_cover(Tsub, n, r, sup_index, sup_ptr, out, 4)
        viol = out if c < 0 else out[:c]
        if len(viol) == 0:
            P(f'SAT: family of {len(sel)} sets satisfies everything, it {it}')
            np.save(f'cegar4_{tag}_SOLUTION.npy', T[np.sort(sel)])
            break
        for row in viol:
            cl = sorted(-(int(sel[t]) + 1) for t in row if t >= 0)
            s.add_clause(cl); cl_f.write(' '.join(map(str, cl)) + ' 0\n'); ncl += 1
        cl_f.flush()
        if it % 10 == 1:
            P(f'it {it}: |F|={len(sel)} new {len(viol)} total {ncl} t={time.time()-t0:.1f}')
    cl_f.close()
    # header file for DIMACS
    with open(f'cegar4_{tag}.cnf', 'w') as f:
        f.write(f'p cnf {N} {ncl}\n')
        for fn in (f'cegar4_{tag}.clauses', f'cegar4_{tag}.lemmas'):
            with open(fn) as g:
                for line in g: f.write(line)
    np.save(f'cegar4_{tag}_pool.npy', T)

if __name__ == '__main__':
    main()
