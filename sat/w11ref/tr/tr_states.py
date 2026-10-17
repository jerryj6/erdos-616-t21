"""enumerate the per-edge state universe. usage: python3 tr_states.py a c [n34]  -> st_<a><c>[n].npz (tr, first, cnt, SB, SO)"""
import sys, numpy as np, time
from tr_core import base, edge_states, pc
a, c = int(sys.argv[1]), int(sys.argv[2]); n34 = (1 if 'n34' in sys.argv else 0) | (2 if 'no24' in sys.argv else 0) | (4 if 'nonk' in sys.argv else 0) | (8 if 'now7' in sys.argv else 0)
names, P, OS = base(a, c); n = len(names); FULL = (1 << n) - 1
t0 = time.time(); buf = np.zeros((40000, 4), np.int64)
tr = []; SB = []; SO = []
for b in range(1 << n):
    k = edge_states(b, P, OS, FULL, n34, buf)
    if k:
        tr.append(b)
        for r in range(k): SB.append(b); SO.append(buf[r].copy())
cnt = np.array([sum(1 for _ in range(0))]) if False else None
tr = np.array(tr, np.int64); SB = np.array(SB, np.int64); SO = np.array(SO, np.int64)
first = np.searchsorted(SB, tr); cnt = np.searchsorted(SB, tr, 'right') - first
tag = f'{a}{c}' + ('n' if n34 & 1 else '') + ('x' if n34 & 2 else '') + ('k' if n34 & 4 else '') + ('w' if n34 & 8 else '')
np.savez(f'st_{tag}.npz', tr=tr, first=first, cnt=cnt, SB=SB, SO=SO, P=P, OS=OS)
sz = np.bincount([pc(int(t)) for t in tr])
print(tag, 'core', n, 'traces', len(tr), 'states', len(SB), 'sizes', {i: int(s) for i, s in enumerate(sz) if s}, 'time %.0fs' % (time.time() - t0))
