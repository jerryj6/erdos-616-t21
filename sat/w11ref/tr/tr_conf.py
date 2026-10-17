"""full conflict matrix (upper triangle) in row chunks. usage: python3 tr_conf.py TAG lo hi [drop] -> cf_TAG[_dD]/r_lo_hi.npy (packed)
A pair (t,t') of traces is a CONFLICT iff no state pair and no integer overlap vector passes pair_rules."""
import sys, os, numpy as np, time
from tr_core import conf_rows
tag, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); drop = int(sys.argv[4]) if len(sys.argv) > 4 else 0
U = np.load(f'st_{tag}.npz'); n34 = (1 if 'n' in tag else 0) | (2 if 'x' in tag else 0) | (4 if 'k' in tag else 0) | (8 if 'w' in tag else 0)
FULL = (1 << int(np.log2(int(U['P'].max())) + 1)) - 1
FULL = int(U['P'][0] | U['P'][1] | U['P'][2] | U['P'][3])
d = f'cf_{tag}' + (f'_d{drop}' if drop else ''); os.makedirs(d, exist_ok=True)
NT = len(U['tr']); hi = min(hi, NT); t0 = time.time()
M = conf_rows(lo, hi, NT, U['first'], U['cnt'], U['SB'], U['SO'], U['P'], U['OS'], FULL, n34, drop)
np.save(f'{d}/r_{lo}_{hi}.tmp.npy', np.packbits(M, axis=1)); os.replace(f'{d}/r_{lo}_{hi}.tmp.npy', f'{d}/r_{lo}_{hi}.npy')
print(tag, drop, lo, hi, 'conflicts', int(M.sum()), 'time %.0fs' % (time.time() - t0), flush=True)
