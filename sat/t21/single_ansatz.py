"""Ansatz search (construction side): core X = M(5) u A'(a) u C'(c); edges: E1=M u A', E2=M u C' (forced),
and 'single' edges {v} u A_G u C_G (|A_G|=|C_G|=4), all other vertices private.  r=21, target tau>=5.
SAT (CEGAR): P1 = every 4-subset of X disjoint from some chosen S; eager: pairs with |S&S'|<=4 forbidden
(L1 lemma); lazy: violating subfamilies (empty intersection, span<=60) found by DFS.
If SAT with no violation -> candidate construction (verify!).  Usage: python single_ansatz.py a c"""
import sys, itertools, time
import numpy as np
from pysat.solvers import Solver
sys.path.insert(0, '..')
from core import find_violations
r = 21
a, c = int(sys.argv[1]), int(sys.argv[2])
n = 5 + a + c
M = list(range(5)); A = list(range(5, 5 + a)); C = list(range(5 + a, n))
bit = lambda L: sum(1 << v for v in L)
E1 = bit(M + A); E2 = bit(M + C)
pool = [E1, E2]
for v in M:
    for AG in itertools.combinations(A, 4):
        for CG in itertools.combinations(C, 4):
            pool.append(bit((v,) + AG + CG))
S = np.array(pool, dtype=np.int64); N = len(S)
pc = lambda x: bin(int(x)).count('1')
s = Solver(name='cadical153')
s.add_clause([1]); s.add_clause([2])
for B in itertools.combinations(range(n), 4):
    bm = bit(B)
    s.add_clause([i + 1 for i in range(N) if (pool[i] & bm) == 0])
npair = 0
T16 = np.array([bin(x).count('1') for x in range(1<<16)], dtype=np.int64)
pcv = lambda z: T16[z & 0xFFFF] + T16[(z >> 16) & 0xFFFF] + T16[(z >> 32) & 0xFFFF]
for i in range(N):
    bad = np.nonzero(pcv(S[i] & S[i+1:]) <= 4)[0] + i + 1
    for j in bad:
        s.add_clause([-(i + 1), -(int(j) + 1)]); npair += 1
print(f'a={a} c={c} n={n} pool={N} pairclauses={npair}', flush=True)
it = 0; t0 = time.time()
while True:
    it += 1
    if not s.solve():
        print(f'UNSAT it={it} t={time.time()-t0:.1f}', flush=True); break
    m = s.get_model()
    sel = [i for i in range(N) if m[i] > 0]
    viol, cnt = find_violations(S[sel], r, 8, 20000)
    if cnt == 0:
        print(f'SAT!! |F|={len(sel)}', flush=True)
        np.save(f'single_a{a}_c{c}_SOL.npy', S[sel]); break
    for row in viol:
        s.add_clause([-(sel[t] + 1) for t in row if t >= 0])
    if it % 20 == 1: print(f'it {it} |F|={len(sel)} viol={cnt} t={time.time()-t0:.1f}', flush=True)
