"""Trace-level conflict graph: traces t != t' conflict iff EVERY state pair (s in t, s' in t') is incompatible (w14_compat).
Computed for one orbit representative r per orbit of the order-576 group and transported: conf(g r, g t') = conf(r, t')
(valid because compat is written in terms of P/N/TRI/OSZ and g permutes them; verified on random pairs by w14_confcheck).
Output: w14_conf.npz with packed bit matrix C[t_index, t'_index]."""
import sys, json, time, numpy as np
sys.path.insert(0, '..')
from w14_group import G, app
from w14_compat import compat
import os as _os
DROP = tuple(x for x in _os.environ.get('W14DROP', '').split(',') if x)
SUF = ('_drop' + '_'.join(DROP)) if DROP else ''
D = json.load(open('w14_states.json'))
T = [b for b, _ in D]; tid = {b: i for i, b in enumerate(T)}
sb = np.array([b for b, s in D for o in s], dtype=np.int64)
so = np.array([o for b, s in D for o in s], dtype=np.int64)
st_t = np.array([i for i, (b, s) in enumerate(D) for o in s])
starts = np.r_[0, np.nonzero(np.diff(st_t))[0] + 1]
NT = len(T)
# orbits
orb_rep = {}; reps = []
for b in T:
    if b in orb_rep: continue
    reps.append(b)
    for p, pi in G: orb_rep[app(p, b)] = b
print('traces', NT, 'orbits', len(reps), flush=True)
C = np.zeros((NT, NT), bool)
t0 = time.time()
Tarr = np.array(T, dtype=np.int64)
# precompute image index arrays for each group element
from w13_enum import n
imgs = []
for p, pi in G:
    pa = np.zeros(1 << n, dtype=np.int64)  # too big? 65536 ok
    imgs.append(p)
def appv(p, arr):
    y = np.zeros_like(arr)
    for a in range(n): y |= ((arr >> a) & 1) << p[a]
    return y
LUT = np.full(1 << n, -1, dtype=np.int64); LUT[Tarr] = np.arange(NT)
TI = {}
for k, (p, pi) in enumerate(G):
    TI[k] = LUT[appv(p, Tarr)]  # TI[k][i] = index of g(T[i])
    assert (TI[k] >= 0).all()
import os
ROWS = f'w14_reprows{SUF}.npy'
R = np.load(ROWS) if os.path.exists(ROWS) else np.zeros((0, NT), bool)
for ri, r in enumerate(reps):
    i = tid[r]; s = D[i][1]
    if ri < len(R): conf = R[ri]
    else:
        M = compat(np.array([r] * len(s), dtype=np.int64), np.array(s, dtype=np.int64), sb, so, DROP)
        anyc = np.logical_or.reduceat(M.any(0), starts)  # per target trace
        conf = ~anyc; conf[i] = False
        R = np.vstack([R, conf[None]])
        if ri % 25 == 24: np.save(ROWS + '.tmp.npy', R); os.replace(ROWS + '.tmp.npy', ROWS)
    for k in range(len(G)):
        C[TI[k][i], TI[k][conf]] = True
    if ri % 20 == 0: print(ri, round(time.time() - t0, 1), int(conf.sum()), flush=True)
np.save(ROWS + '.tmp.npy', R); os.replace(ROWS + '.tmp.npy', ROWS)
sym = (C == C.T).all()
print('symmetric', sym, 'conflict pairs', int(C.sum()) // 2, 'density', C.sum() / NT / NT, flush=True)
np.savez_compressed(f'w14_conf{SUF}.npz', C=np.packbits(C, axis=1), T=Tarr)
