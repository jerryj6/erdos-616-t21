"""Φ for a pair-family drop control: COV as tr_cnf.py, CONF = conflict pairs still conflicts without the family.
usage: python3 tr_cnfd.py TAG DROP OUT"""
import sys, glob, itertools, numpy as np
tag, drop, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; NT = len(tr); n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
pairs = np.load(f'pairs_{tag}.npy')
keep = np.zeros(len(pairs), bool)
for f in glob.glob(f'cfd_{tag}_{drop}/p_*_*.npy'):
    if 'tmp' in f: continue
    lo, hi = map(int, f.split('/')[-1][2:-4].split('_')); keep[lo:hi] = np.load(f)
pairs = pairs[keep]
need = [B for B in (sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))]
cov = [[i + 1 for i in np.nonzero((tr & B) == 0)[0]] for B in need]
with open(out, 'w') as fh:
    fh.write(f'p cnf {NT} {len(cov) + len(pairs)}\n')
    for c in cov: fh.write(' '.join(map(str, c)) + ' 0\n')
    np.savetxt(fh, np.stack([-(pairs[:, 0] + 1), -(pairs[:, 1] + 1), np.zeros(len(pairs), np.int64)], 1), fmt='%d')
print(tag, 'drop', drop, 'CONF kept', len(pairs), 'of', len(keep), '->', out)
