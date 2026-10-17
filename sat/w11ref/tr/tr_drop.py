"""drop-one controls for PAIR-rule families: re-test every conflict pair of the full matrix cf_TAG with pair rules minus
family `drop` (dropping a rule can only turn conflicts into compatibilities, so only conflict pairs need re-testing).
Also, with a CORE (drat-trim -c output), reports how many core CONF clauses stop being conflicts (dependency).
usage: python3 tr_drop.py TAG DROP [lo hi]  -> cfd_TAG_DROP/p_lo_hi.npy (bool: still conflict) ; resumable chunks of pairs"""
import sys, os, glob, numpy as np, numba as nb, time
from tr_core import trace_pair_compat
tag, drop = sys.argv[1], int(sys.argv[2])
U = np.load(f'st_{tag}.npz'); NT = len(U['tr'])
n34 = (1 if 'n' in tag else 0) | (2 if 'x' in tag else 0) | (4 if 'k' in tag else 0) | (8 if 'w' in tag else 0)
FULL = int(U['P'][0] | U['P'][1] | U['P'][2] | U['P'][3])
if not os.path.exists(f'pairs_{tag}.npy'):
    pr = []; lo = 0
    files = {int(f.split('/')[-1][2:-4].split('_')[0]): f for f in glob.glob(f'cf_{tag}/r_*_*.npy') if 'tmp' not in f}
    while lo < NT:
        R = np.unpackbits(np.load(files[lo]), axis=1)[:, :NT]; r, c = np.nonzero(R)
        pr.append(np.stack([r + lo, c], 1)); lo += len(R)
    np.save(f'pairs_{tag}.npy', np.concatenate(pr))
PF = [x[10:] for x in sys.argv if x.startswith('pairsfile=')]
pairs = np.load(PF[0]) if PF else np.load(f'pairs_{tag}.npy')
@nb.njit(cache=True)
def run(pairs, first, cnt, SB, SO, P, OS, FULL, n34, drop):
    out = np.zeros(len(pairs), np.bool_)
    for r in range(len(pairs)):
        out[r] = not trace_pair_compat(pairs[r, 0], pairs[r, 1], first, cnt, SB, SO, P, OS, FULL, n34, drop)
    return out
d = f'cfd_{tag}_{drop}' + ('_' + PF[0].split('.')[0] if PF else ''); os.makedirs(d, exist_ok=True); CH = 500000
for lo in range(0, len(pairs), CH):
    hi = min(lo + CH, len(pairs)); f = f'{d}/p_{lo}_{hi}.npy'
    if os.path.exists(f): continue
    t0 = time.time()
    res = run(pairs[lo:hi], U['first'], U['cnt'], U['SB'], U['SO'], U['P'], U['OS'], FULL, n34, drop)
    np.save(f + '.tmp.npy', res); os.replace(f + '.tmp.npy', f)
    print(tag, drop, lo, hi, 'still conflict', int(res.sum()), 'of', hi - lo, '%.0fs' % (time.time() - t0), flush=True)
open(f'{d}.done', 'w').close()
