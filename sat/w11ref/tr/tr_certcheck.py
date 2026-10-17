"""check the 8 tree certificates' CNFs against Φ: every positive clause is exactly one COV(B) (avoider list recomputed from the
universe) or the unit x_r of that case's orbit representative; all 1325 COV present; every binary clause is a negative pair
in the full conflict list pairs_TAG.npy; nothing else. Also re-asserts the root step: the plan's orbit representatives'
Stab(B*)-orbits cover all avoiders of B*, and B* is a needed 4-set.   usage: python3 tr_certcheck.py TAG"""
import sys, json, itertools, numpy as np
from tr_sym import gens, group, apply
tag = sys.argv[1]; a, c = int(tag[0]), int(tag[1])
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; NT = len(tr); n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
need = [B for B in (sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))]
cov = {frozenset((np.nonzero((tr & B) == 0)[0] + 1).tolist()) for B in need}
pairs = np.load(f'pairs_{tag}.npy'); key = np.sort((pairs[:, 0] + 1) * (NT + 1) + (pairs[:, 1] + 1))
pl = json.load(open(f'case_{tag}_plan.json')); Bs = pl['Bstar']
assert Bs in need
names, Pm, OS, G = gens(a, c); E = group(G, n); stab = [e for e in E if apply(e, Bs) == Bs]
lut = {int(t): i for i, t in enumerate(tr)}
orb = set()
for r, _ in pl['reps']: orb |= {lut[apply(e, int(tr[r]))] for e in stab}
print('B*', Bs, 'needed', True, '|Stab|', len(stab), 'orbits of reps cover avoiders of B*:', orb == set(np.nonzero((tr & Bs) == 0)[0].tolist()))
for K, (r, _) in enumerate(pl['reps']):
    pos = []; bi = []; other = 0
    with open(f'tree_{tag}_{K}.cnf') as fh:
        next(fh)
        for line in fh:
            L = [int(x) for x in line.split()[:-1]]
            if all(x > 0 for x in L): pos.append(frozenset(L))
            elif len(L) == 2 and L[0] < 0 and L[1] < 0: bi.append(sorted((-L[0], -L[1])))
            else: other += 1
    bi = np.array(bi, np.int64); k = bi[:, 0] * (NT + 1) + bi[:, 1]
    inconf = np.isin(k, key).all()
    units = [p for p in pos if len(p) == 1]; covs = [p for p in pos if len(p) > 1]
    print(f'tree_{tag}_{K}: COV clauses {len(covs)} all in Φ {all(p in cov for p in covs)} complete {set(covs) == cov}, '
          f'units {[sorted(u) for u in units]} == x_r {units == [frozenset([r + 1])]}, binary {len(bi)} all CONF of Φ {bool(inconf)}, other {other}')
