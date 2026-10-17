"""Independent semantic check of a #616 certificate CNF (pure Python sets, no shared code).
Claim encoded: there is no r-uniform hypergraph with the local property (every edge subfamily spanning <= 3r-3
vertices has a common vertex) and tau >= K whose degree>=2 vertex set ('core') X=[n] has every edge-core
S_i with |X \\ S_i| in [cmin,cmax]  (i.e. the choice of family of complements T = X \\ S is UNSAT).
Checks: (1) clauses with positive literals are exactly the P1 clauses: for each (K-1)-subset C of [n],
the disjunction of all pool T containing C, and every (K-1)-subset appears;
(2) every all-negative clause {T_1..T_m} is a violating subfamily: building literal edges
E_i = S_i u {r-|S_i| private vertices}, the E_i have empty common intersection and |U E_i| <= 3r-3.
Usage: python verify_cnf.py cnf pool.npy n r K"""
import sys, itertools
import numpy as np
cnf, poolf = sys.argv[1], sys.argv[2]
n, r, K = map(int, sys.argv[3:6])
T = [int(x) for x in np.load(poolf)]
X = frozenset(range(n))
Tset = [frozenset(v for v in range(n) if (t >> v) & 1) for t in T]
def edge(i):
    S = X - Tset[i]
    return set(S) | {('priv', i, j) for j in range(r - len(S))}
want = {}
for C in itertools.combinations(range(n), K - 1):
    want[frozenset(C)] = frozenset(i + 1 for i in range(len(T)) if set(C) <= Tset[i])
seenP1 = set(); bad = 0; nneg = 0
with open(cnf) as f:
    hdr = next(f)
    for line in f:
        lits = list(map(int, line.split()))
        assert lits[-1] == 0; lits = lits[:-1]
        if all(l > 0 for l in lits):
            st = frozenset(lits)
            # find which C it is: intersection of the T's must contain a C with want[C]==st
            common = frozenset.intersection(*[Tset[l - 1] for l in lits])
            ok = any(want.get(frozenset(C)) == st for C in itertools.combinations(sorted(common), K - 1))
            if not ok: bad += 1
            for C in itertools.combinations(sorted(common), K - 1):
                if want.get(frozenset(C)) == st: seenP1.add(frozenset(C))
        elif all(l < 0 for l in lits):
            nneg += 1
            E = [edge(-l - 1) for l in lits]
            if set.intersection(*E) or len(set().union(*E)) > 3 * r - 3:
                bad += 1
        else:
            bad += 1
print(f'header {hdr.strip()}; P1 covered {len(seenP1)}/{len(want)}; blocking clauses {nneg}; bad clauses {bad}')
print('SEMANTICS OK' if bad == 0 and len(seenP1) == len(want) else 'SEMANTICS FAIL')
