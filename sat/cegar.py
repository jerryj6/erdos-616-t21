"""CEGAR SAT search: does an r-uniform hypergraph with local property L_r and tau>=k exist
whose degree>=2 vertex set ('core') has n vertices? (complement formulation: T_i = X \\ S_i).
Usage: python cegar.py r k n [cmin cmax] [--sym] """
import sys, time, json, itertools
import numpy as np
from pysat.solvers import Solver
from core import find_violations

def main():
    r, k, n = map(int, sys.argv[1:4])
    rest = [a for a in sys.argv[4:] if not a.startswith('--')]
    cmin = int(rest[0]) if rest else k - 1
    cmax = int(rest[1]) if len(rest) > 1 else n - 2 * k + 1
    log = open(f'log_r{r}_k{k}_n{n}_c{cmin}-{cmax}.txt', 'w')
    def P(*a):
        s = ' '.join(map(str, a)); print(s); log.write(s + '\n'); log.flush()
    X = (1 << n) - 1
    Ts = [sum(1 << v for v in c) for size in range(cmin, cmax + 1) for c in itertools.combinations(range(n), size)]
    Ts = np.array(Ts, dtype=np.int64)
    Ss = X ^ Ts
    N = len(Ts)
    var = lambda i: int(i) + 1
    P(f'r={r} k={k} n={n} csizes {cmin}..{cmax} vars={N}')
    clauses = []
    # P1
    for C in itertools.combinations(range(n), k - 1):
        cm = sum(1 << v for v in C)
        lits = [var(i) for i in np.nonzero((Ts & cm) == cm)[0]]
        clauses.append(lits)
    # eager pairs: |S1 & S2| <= k-1 forbidden (implied), also catches empty intersections
    pc = np.array([bin(x).count('1') for x in range(1 << 16)], dtype=np.int64)
    def popv(a):
        return pc[a & 0xFFFF] + pc[(a >> 16) & 0xFFFF]
    npair = 0
    for i in range(N):
        inter = Ss[i] & Ss[i+1:]
        bad = np.nonzero(popv(inter) <= k - 1)[0]
        for j in bad:
            clauses.append([-var(i), -var(i + 1 + j)]); npair += 1
    P('P1 clauses', len(clauses) - npair, 'pair clauses', npair)
    s = Solver(name='cadical153', bootstrap_with=clauses)
    allcl = list(clauses)
    it = 0; t0 = time.time()
    while True:
        it += 1
        ok = s.solve()
        if not ok:
            P(f'UNSAT after {it} iterations, {time.time()-t0:.1f}s, total clauses {len(allcl)}')
            json.dump({'r': r, 'k': k, 'n': n, 'cmin': cmin, 'cmax': cmax, 'result': 'UNSAT', 'nvars': N,
                       'clauses': allcl}, open(f'cnf_r{r}_k{k}_n{n}_c{cmin}-{cmax}.json', 'w'))
            return
        m = s.get_model()
        sel = [i for i in range(N) if m[i] > 0]
        F = Ss[sel]
        viol, cnt = find_violations(F, r, 8, 200000)
        if cnt == 0:
            P(f'SAT: found family of {len(sel)} core sets after {it} iterations')
            json.dump({'r': r, 'k': k, 'n': n, 'result': 'SAT', 'S': [int(x) for x in F]},
                      open(f'sol_r{r}_k{k}_n{n}_c{cmin}-{cmax}.json', 'w'))
            return
        for row in viol:
            cl = [-var(sel[t]) for t in row if t >= 0]
            s.add_clause(cl); allcl.append(cl)
        if it % 10 == 1:
            P(f'it {it}: |F|={len(sel)} violations {cnt} added {len(viol)} t={time.time()-t0:.1f}')

if __name__ == '__main__':
    main()
