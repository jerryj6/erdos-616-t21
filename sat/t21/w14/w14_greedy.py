"""Randomised greedy search for a pairwise-compatible cover (a model of Phi restricted to gac-alive traces).
Finding one shows Phi (pairwise level) is SAT; it is not a realization."""
import sys, json, itertools, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T)
C = np.unpackbits(z['C'], axis=1)[:, :NT].astype(bool)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = np.array([B for B in Bs if not any((P[i] & B) == 0 for i in range(4))], dtype=np.int64)
al = set(json.load(open('w14_gac_elim.json'))['alive'])
alive0 = np.array([int(t) in al for t in T])
AV = ((T[:, None] & need[None, :]) == 0)  # NT x 1730
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
best = None
for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 20):
    cand = alive0.copy(); unc = np.ones(len(need), bool); S = []
    while unc.any():
        gain = AV[:, unc].sum(1) * cand
        if gain.max() == 0: break
        # pick among near-best with noise
        sc = gain + rng.random(NT) * 3
        sc[~cand] = -1
        i = int(np.argmax(sc)); S.append(i)
        unc &= ~AV[i]; cand &= ~C[i]; cand[i] = False
    left = int(unc.sum())
    if best is None or left < best[0]: best = (left, S)
    print('trial', trial, 'chosen', len(S), 'uncovered left', left, flush=True)
    if left == 0:
        json.dump([int(T[i]) for i in S], open('w14_greedy_cover.json', 'w')); print('PAIRWISE MODEL FOUND'); break
