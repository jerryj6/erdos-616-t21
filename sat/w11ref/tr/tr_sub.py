"""SUB-FORMULA of Φ_TAG: all COV clauses + a deterministic random fraction FRAC of the CONF clauses (seed SEED).
Every clause is a clause of phi_TAG.cnf, so UNSAT of the sub-formula implies UNSAT of Φ (smaller certificate).
usage: python3 tr_sub.py TAG FRAC SEED OUT"""
import sys, itertools, numpy as np
tag, frac, seed, out = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; NT = len(tr); n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
pairs = np.load(f'pairs_{tag}.npy')
pairs = pairs[np.random.default_rng(seed).random(len(pairs)) < frac]
need = [B for B in (sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))]
cov = [[i + 1 for i in np.nonzero((tr & B) == 0)[0]] for B in need]
with open(out, 'w') as fh:
    fh.write(f'p cnf {NT} {len(cov) + len(pairs)}\n')
    for c in cov: fh.write(' '.join(map(str, c)) + ' 0\n')
    np.savetxt(fh, np.stack([-(pairs[:, 0] + 1), -(pairs[:, 1] + 1), np.zeros(len(pairs), np.int64)], 1), fmt='%d')
print(tag, 'frac', frac, 'seed', seed, 'COV', len(cov), 'CONF', len(pairs), '->', out)
