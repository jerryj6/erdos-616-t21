import json, collections
from w13_enum import *
feas = json.load(open('w13_feas.json'))
base_types = {}
out = {}
for (i,j),Nij in N.items():
    for x in bits(Nij):
        if any(base_single(k,i,j)==(1<<x) for k in range(4) if k not in (i,j)): continue
        L=[b for b in feas if (b & Nij)==(1<<x)]
        AND=(1<<n)-1; OR=0
        for b in L: AND&=b; OR|=b
        key=f'({i},{j}):{NAMES[x]}'
        out[key]=L
        # o-vectors summary over all traces
        print(f'{key:12s} #traces {len(L):4d} forced-in {nm(AND)} forced-out {nm(((1<<n)-1)&~OR)}')
json.dump(out, open('w13_singles.json','w'))
