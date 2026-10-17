"""Dominance reduction of the pairwise trace model (PROVED sound for UNSAT):
model = choose a set S of traces, pairwise non-conflicting, such that every core 4-set B not avoided by a base edge
is avoided by some t in S.
(D0) a trace avoiding no needed B can be deleted from any solution.
(D1) if t* strictly subset of t (so t* avoids every B that t avoids), both remaining, and every remaining conflict
neighbour of t* other than t is a conflict neighbour of t, then replacing t by t* in any solution gives a solution;
so deleting t preserves satisfiability. Applied sequentially against the CURRENT remaining set."""
import sys, json, itertools, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T)
Cp = z['C']  # packed rows (uint8)
C = np.unpackbits(Cp, axis=1)[:, :NT].astype(bool)
core = (1 << n) - 1
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = [B for B in Bs if not any((P[i] & B) == 0 for i in range(4))]
needA = np.array(need, dtype=np.int64)
cov = np.array([((needA & t) == 0).any() for t in T])
rem = cov.copy()
print('needed B', len(need), 'traces', NT, 'after D0', rem.sum(), flush=True)
LUT = {int(t): i for i, t in enumerate(T)}
order = sorted(range(NT), key=lambda i: -bin(int(T[i])).count('1'))  # try to delete big traces first
removed = 0; dom = {}
def packed(mask): return np.packbits(mask)
changed = True; rnd = 0
while changed:
    changed = False; rnd += 1
    remP = packed(rem)
    for i in order:
        if not rem[i]: continue
        t = int(T[i])
        bits_ = [a for a in range(n) if t >> a & 1]
        for k in (len(bits_) - 1, len(bits_) - 2):
            if k < 1: continue
            hit = False
            for sub in itertools.combinations(bits_, k):
                j = LUT.get(sum(1 << a for a in sub))
                if j is None or not rem[j]: continue
                extra = Cp[j] & remP & ~Cp[i]
                if extra.any():
                    ex = np.unpackbits(extra)[:NT]; ex[i] = 0
                    if ex.any(): continue
                rem[i] = False; remP = packed(rem); removed += 1; dom[i] = j; hit = True; changed = True; break
            if hit: break
    print('round', rnd, 'removed', removed, flush=True)
print('removed by D1', removed, 'remaining', int(rem.sum()), flush=True)
sub = np.nonzero(rem)[0]
Cs = C[np.ix_(sub, sub)]
print('conflict pairs in reduced', int(Cs.sum()) // 2, flush=True)
np.savez_compressed('w14_red.npz', idx=sub, dom=np.array(list(dom.items())))
