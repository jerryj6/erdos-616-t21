"""Eager enumeration of ALL violating subfamilies (size 2,3,4) among the candidate pool
for the complement formulation of Erdos #616, target tau >= 5.
Pool: subsets T of [n] (T = X \\ S, S = core part of an edge) with sizes cmin..cmax.
A subfamily {T_1..T_m} is violating iff union T = X (the S's have empty intersection) and
span = |U S| + sum (r - |S_i|) <= 3r-3.
Blocking clauses are emitted for violating pairs, for violating triples with no covering pair,
and for violating quadruples with no covering sub-pair/sub-triple (supersets of a violating family
are blocked by it; span is monotone so minimal empty-intersection subfamilies suffice).
Caller must verify separately that no minimal violating family of size >= 5 exists for (n,r,cmin,cmax).
Writes DIMACS CNF: vars = pool indices + 1; P1 clauses (every 4-subset of [n] lies in a chosen T);
blocking clauses."""
import sys, itertools, time
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
def enum(T, n, r, out2, out3, out4, sup_index, sup_ptr):
    X = (1 << n) - 1
    N = T.shape[0]
    lim = 3 * r - 3
    n2 = 0; n3 = 0; n4 = 0
    for i in range(N):
        Si = X ^ T[i]
        for j in range(i + 1, N):
            u2 = T[i] | T[j]
            Sj = X ^ T[j]
            sp2 = popc(Si | Sj) + 2 * r - popc(Si) - popc(Sj)
            if u2 == X:
                if sp2 <= lim:
                    if n2 < out2.shape[0]:
                        out2[n2, 0] = i; out2[n2, 1] = j
                    n2 += 1
                continue
            for k in range(j + 1, N):
                if (T[i] | T[k]) == X or (T[j] | T[k]) == X:
                    continue
                u3 = u2 | T[k]
                Sk = X ^ T[k]
                sp3 = popc(Si | Sj | Sk) + 3 * r - popc(Si) - popc(Sj) - popc(Sk)
                if sp3 > lim:
                    continue
                if u3 == X:
                    if n3 < out3.shape[0]:
                        out3[n3, 0] = i; out3[n3, 1] = j; out3[n3, 2] = k
                    n3 += 1
                    continue
                R = X ^ u3
                low = 0
                while not (R >> low) & 1:
                    low += 1
                for p in range(sup_ptr[low], sup_ptr[low + 1]):
                    l = sup_index[p]
                    if l <= k:
                        continue
                    if (T[l] & R) != R:
                        continue
                    if (T[i] | T[l]) == X or (T[j] | T[l]) == X or (T[k] | T[l]) == X:
                        continue
                    if (T[i] | T[j] | T[l]) == X or (T[i] | T[k] | T[l]) == X or (T[j] | T[k] | T[l]) == X:
                        continue
                    Sl = X ^ T[l]
                    sp4 = popc(Si | Sj | Sk | Sl) + 4 * r - popc(Si) - popc(Sj) - popc(Sk) - popc(Sl)
                    if sp4 <= lim:
                        if n4 < out4.shape[0]:
                            out4[n4, 0] = i; out4[n4, 1] = j; out4[n4, 2] = k; out4[n4, 3] = l
                        n4 += 1
    return n2, n3, n4

def build(n, r, cmin, cmax, cap4=40_000_000):
    Ts = [sum(1 << v for v in cc) for size in range(cmin, cmax + 1) for cc in itertools.combinations(range(n), size)]
    T = np.array(Ts, dtype=np.int64)
    N = len(T)
    lists = [np.nonzero((T >> v) & 1)[0] for v in range(n)]
    sup_ptr = np.zeros(n + 1, np.int64)
    for v in range(n):
        sup_ptr[v + 1] = sup_ptr[v] + len(lists[v])
    sup_index = np.concatenate(lists).astype(np.int64)
    out2 = np.zeros((2_000_000, 2), np.int32)
    out3 = np.zeros((20_000_000, 3), np.int32)
    out4 = np.zeros((cap4, 4), np.int32)
    t0 = time.time()
    n2, n3, n4 = enum(T, n, r, out2, out3, out4, sup_index, sup_ptr)
    print(f'n={n} r={r} c={cmin}..{cmax} pool={N}: pairs {n2} triples {n3} quads {n4}  ({time.time()-t0:.1f}s)', flush=True)
    assert n2 <= out2.shape[0] and n3 <= out3.shape[0] and n4 <= out4.shape[0]
    return T, out2[:n2], out3[:n3], out4[:n4]

def write_cnf(path, n, k, T, o2, o3, o4):
    N = len(T)
    P1 = []
    for C in itertools.combinations(range(n), k - 1):
        cm = sum(1 << v for v in C)
        P1.append(np.nonzero((T & cm) == cm)[0] + 1)
    ncl = len(P1) + len(o2) + len(o3) + len(o4)
    with open(path, 'w') as f:
        f.write(f'p cnf {N} {ncl}\n')
        for lits in P1:
            f.write(' '.join(map(str, lits)) + ' 0\n')
        for arr in (o2, o3, o4):
            if len(arr):
                neg = -(arr.astype(np.int64) + 1)
                np.savetxt(f, np.hstack([neg, np.zeros((len(arr), 1), np.int64)]), fmt='%d')
    return ncl

if __name__ == '__main__':
    n, r, cmin, cmax = map(int, sys.argv[1:5])
    T, o2, o3, o4 = build(n, r, cmin, cmax)
    path = f'eager_r{r}_k5_n{n}_c{cmin}-{cmax}.cnf'
    ncl = write_cnf(path, n, 5, T, o2, o3, o4)
    np.save(path.replace('.cnf', '_pool.npy'), T)
    print('wrote', path, 'clauses', ncl, flush=True)
