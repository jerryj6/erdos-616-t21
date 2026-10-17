"""Re-check a drop-one control model (w14_lazy_stall_drop<f>.json) directly: it must cover every needed core 4-set and its
traces must be pairwise compatible under w14_compat.compat(drop=(f,)) computed directly (no group transport), and must contain
at least one pair that IS a conflict under the full rules (otherwise it would be a model of Phi itself).
Usage: python3 w14_ctrl_check.py f"""
import sys, json, itertools, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n
from w14_compat import compat
f = sys.argv[1]
S = json.load(open(f'w14_lazy_stall_drop{f}.json'))
ST = {b: s for b, s in json.load(open('w14_states.json'))}
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = [B for B in Bs if not any((P[i] & B) == 0 for i in range(4))]
cov = all(any((B & t) == 0 for t in S) for B in need)
bad_drop = 0; conf_full = 0
for x, y in itertools.combinations(S, 2):
    a = (np.array([x] * len(ST[x])), np.array(ST[x])); b = (np.array([y] * len(ST[y])), np.array(ST[y]))
    if not compat(a[0], a[1], b[0], b[1], (f,)).any(): bad_drop += 1
    if not compat(a[0], a[1], b[0], b[1]).any(): conf_full += 1
print(f'drop {f}: cover size {len(S)}, covers all {len(need)} needed B: {cov}; pairs conflicting WITHOUT {f}: {bad_drop} (must be 0); '
      f'pairs conflicting under FULL rules: {conf_full} (>0 expected)')
