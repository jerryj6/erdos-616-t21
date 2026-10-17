import json, itertools, collections
from w13_enum import *
feas = json.load(open('w13_feas.json')); S = json.load(open('w13_singles.json'))
FULL=(1<<n)-1
res=[]
for Bt in itertools.combinations(range(n),4):
    B=sum(1<<a for a in Bt)
    av=[b for b in feas if not b & B]
    hit_all = all(all(b & B for b in L) for L in S.values())
    nmiss = sum(1 for L in S.values() if not all(b & B for b in L))   # single types that CAN avoid B
    AND=FULL; 
    for b in av: AND&=b
    roles=collections.Counter()
    for b in av:
        r=tuple(sorted(f'{i}{j}' for (i,j),Nij in N.items() if pc(b&Nij)==1))
        roles[r]+=1
    res.append(dict(B=[NAMES[a] for a in Bt], nav=len(av), hit_all=hit_all, nmiss=nmiss, forced=[NAMES[a] for a in bits(AND)], roles=dict((','.join(k) or '-',v) for k,v in roles.items())))
print('min nav', min(r['nav'] for r in res))
H=[r for r in res if r['hit_all']]
print('B hit by every first-gen single trace:', len(H))
for r in sorted(H,key=lambda r:r['nav'])[:60]: print(r['nav'], r['B'], 'forced', r['forced'], r['roles'])
json.dump(res, open('w13_B.json','w'))
