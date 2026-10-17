"""Positive control for w14_indep.feasible_pair: every pair of non-base edges of the literal K4 realizations must be feasible."""
import sys, json
sys.path.insert(0, '..')
from w14_indep import feasible_pair
from w13_enum import W8
idx = {s: a for a, s in enumerate(W8)}
files = ['w12_M10_real_keep.json','w11_B_real_keep.json','w10x_w12b1_real.json','w10x_w12Br1_real.json','w10x_w12Br2_real.json',
         'w10x_w12Pr0_real.json','w10x_w12Pr1_real.json','w10x_w12Pr2_real.json','w10x_w12Tr0_real.json','w10x_w12Tr1_real.json',
         'w10x_w12Ur0_real.json','w10x_w12m1_real.json']
tot = bad = 0
for f in files:
    d = json.load(open('../' + f)); names = d.get('names') or d.get('named'); E = []
    for lab, e in zip(d['labels'], d['edges']):
        if lab in ('B0','B1','B2','B3','P0','P1','P2','P3'): continue
        Sn = [(names[x] if x < len(names) else 'U') if isinstance(x, int) else x for x in e]
        E.append((sum(1 << idx[s] for s in Sn if s in idx), [sum(1 for s in Sn if s.startswith(f'O{i}_')) for i in range(4)]))
    for x in range(len(E)):
        for y in range(x + 1, len(E)):
            tot += 1
            if not feasible_pair(E[x][0], E[x][1], E[y][0], E[y][1]): bad += 1; print('REJECTED', f, x, y)
print('pairs', tot, 'rejected', bad)
