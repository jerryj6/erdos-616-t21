# soundness control: every non-base edge of every literally verified realization must pass w13_enum.check
import json, glob
from w13_enum import *
idx = {s:a for a,s in enumerate(W8)}
tot=bad=0
for f in ['w12_M10_real_keep.json','w11_B_real_keep.json','w10x_w12b1_real.json','w10x_w12Br1_real.json','w10x_w12Br2_real.json']:
    d=json.load(open(f)); names=d.get('names') or d.get('named')
    for lab,e in zip(d['labels'],d['edges']):
        if lab in ('B0','B1','B2','B3','P0','P1','P2','P3'): continue
        S=[(names[x] if x<len(names) else 'U') if isinstance(x,int) else x for x in e]
        b=sum(1<<idx[s] for s in S if s in idx); o=[sum(1 for s in S if s.startswith(f'O{i}_')) for i in range(4)]
        r=check(b,o); tot+=1
        if r: bad+=1; print(f,lab,nm(b),o,r)
print('edges checked',tot,'violations',bad)
