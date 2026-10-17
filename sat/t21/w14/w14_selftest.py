"""Soundness control for w14_states / w14_compat against every literally verified K4 realization:
each non-base edge's state must be enumerated, and every pair of non-base edges with DIFFERENT core traces
(and also equal traces) must be declared compatible."""
import sys, json, numpy as np
sys.path.insert(0, '..')
from w13_enum import W8, check, nm
from w14_compat import compat
idx = {s: a for a, s in enumerate(W8)}
ST = {b: set(map(tuple, s)) for b, s in json.load(open('w14_states.json'))}
files = ['w12_M10_real_keep.json','w11_B_real_keep.json','w10x_w12b1_real.json','w10x_w12Br1_real.json','w10x_w12Br2_real.json',
         'w10x_w12Pr0_real.json','w10x_w12Pr1_real.json','w10x_w12Pr2_real.json','w10x_w12Tr0_real.json','w10x_w12Tr1_real.json',
         'w10x_w12Ur0_real.json','w10x_w12m1_real.json']
ne = npairs = bad = 0
for f in files:
    d = json.load(open('../' + f)); names = d.get('names') or d.get('named')
    E = []
    for lab, e in zip(d['labels'], d['edges']):
        if lab in ('B0','B1','B2','B3','P0','P1','P2','P3'): continue
        S = [(names[x] if x < len(names) else 'U') if isinstance(x, int) else x for x in e]
        b = sum(1 << idx[s] for s in S if s in idx); o = tuple(sum(1 for s in S if s.startswith(f'O{i}_')) for i in range(4))
        ne += 1
        if b not in ST or o not in ST[b]: bad += 1; print('STATE MISSING', f, lab, nm(b), o, check(b, list(o)))
        E.append((lab, b, o))
    for x in range(len(E)):
        for y in range(x + 1, len(E)):
            npairs += 1
            r = compat(np.array([E[x][1]]), np.array([E[x][2]]), np.array([E[y][1]]), np.array([E[y][2]]))[0, 0]
            if not r: bad += 1; print('PAIR REJECTED', f, E[x][0], E[y][0])
print('files', len(files), 'edges', ne, 'pairs', npairs, 'violations', bad)
