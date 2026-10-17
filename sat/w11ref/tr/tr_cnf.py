"""build Φ for TAG: var i+1 <-> trace tr[i].
 COV(B): for every core 4-set B meeting all four base edges: OR of all traces avoiding B.
 CONF:   ¬x_t ∨ ¬x_t' for every conflict pair of the full matrix cf_TAG[_dD]/.
 extra units: optional list of trace bitmasks forced true (case split).
usage: python3 tr_cnf.py TAG OUT.cnf [drop] [unit=b1,b2,...]"""
import sys, glob, itertools, numpy as np
from tr_core import pc
tag, out = sys.argv[1], sys.argv[2]
drop = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3].isdigit() else 0
units = []
for a in sys.argv[3:]:
    if a.startswith('unit='): units = [int(x) for x in a[5:].split(',') if x]
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; NT = len(tr)
n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
d = f'cf_{tag}' + (f'_d{drop}' if drop else '')
rows = {}
for f in glob.glob(f'{d}/r_*_*.npy'):
    if f.endswith('.tmp.npy'): continue
    lo, hi = map(int, f.split('/')[-1][2:-4].split('_')); rows[lo] = (hi, f)
lo = 0; pairs = []
while lo < NT:
    hi, f = rows[lo]
    M = np.unpackbits(np.load(f), axis=1)[:, :NT]
    r, c = np.nonzero(M); assert np.all(c > r + lo - 1) and np.all(c != r + lo)
    pairs.append(np.stack([r + lo, c], 1)); lo = hi
pairs = np.concatenate(pairs)
need = [B for B in (sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))]
lut = {int(t): i + 1 for i, t in enumerate(tr)}
cov = [[i + 1 for i in np.nonzero((tr & B) == 0)[0]] for B in need]
with open(out, 'w') as fh:
    fh.write(f'p cnf {NT} {len(cov) + len(pairs) + len(units)}\n')
    for c in cov: fh.write(' '.join(map(str, c)) + ' 0\n')
    for u in units: fh.write(f'{lut[u]} 0\n')
    np.savetxt(fh, np.stack([-(pairs[:, 0] + 1), -(pairs[:, 1] + 1), np.zeros(len(pairs), np.int64)], 1), fmt='%d')
print(tag, 'vars', NT, 'needed B', len(need), 'empty COV', sum(1 for c in cov if not c), 'min COV', min(len(c) for c in cov),
      'CONF', len(pairs), 'units', len(units), '->', out)
