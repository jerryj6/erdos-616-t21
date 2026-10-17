"""REFEREE: my own FULL conflict matrix over all 18217 traces (rows lo..hi, all j != i), compared with the authors'
w14_conf.npz['C'] (data). usage: python3 ref_fullconf.py lo hi  -> fc_<lo>_<hi>.npz (packed rows) + counts."""
import sys, numpy as np, numba as nb
from pairref import load_states, feasible, P, OS
first, cnt, B, O = load_states('ref_states.npz')
NT = 18217

@nb.njit(cache=True)
def rows(lo, hi, first, cnt, B, O, P, OS, NT):
    M = np.zeros((hi - lo, NT), np.uint8)
    for a in range(lo, hi):
        for c in range(NT):
            if c == a: continue
            comp = False
            for i in range(first[a + 1], first[a + 1] + cnt[a + 1]):
                for j in range(first[c + 1], first[c + 1] + cnt[c + 1]):
                    if feasible(B[i], O[i], B[j], O[j], P, OS, 0):
                        comp = True; break
                if comp: break
            if not comp: M[a - lo, c] = 1
    return M

lo, hi = int(sys.argv[1]), int(sys.argv[2])
M = rows(lo, hi, first, cnt, B, O, P, OS, NT)
C = np.unpackbits(np.load('../w14/w14_conf.npz')['C'][lo:hi], axis=1)[:, :NT]
mine = M.astype(bool); th = C.astype(bool)
np.savez_compressed(f'fc_{lo}_{hi}.npz', M=np.packbits(M, axis=1))
print(lo, hi, 'mine', int(mine.sum()), 'theirs', int(th.sum()), 'theirs&~mine', int((th & ~mine).sum()), 'mine&~theirs', int((mine & ~th).sum()), flush=True)
