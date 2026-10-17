import json, itertools, collections
from w13_enum import *
from w13_tau import orbit
feas=json.load(open('w13_feas.json'))
def roles(b):
    fg=[];bt=[]
    for (i,j),Nij in N.items():
        s=b&Nij
        if pc(s)!=1: continue
        base=any(base_single(k,i,j)==s for k in range(4) if k not in (i,j))
        (bt if base else fg).append(f'{i}{j}:{nm(s)}')
    return fg,bt
R=[];seen=set()
for Bt in itertools.combinations(range(n),4):
    B=sum(1<<a for a in Bt)
    if B in seen: continue
    orb=orbit(B); seen|=orb
    if not all(B&P[i] for i in range(4)): continue
    av=[b for b in feas if not b&B]
    nfg=sum(1 for b in av if not roles(b)[0])
    multi=sum(1 for b in av if not roles(b)[0] and not roles(b)[1])
    fgtypes=collections.Counter(t for b in av for t in roles(b)[0])
    R.append((nfg==len(av), len(av), nfg, multi, nm(B), len(orb), dict(fgtypes)))
R.sort(key=lambda r:(-r[0], -r[2]/max(1,r[1]), r[1]))
print('base-transversal orbits',len(R))
for r in R[:40]: print(r[:6], list(r[6].items())[:6])
json.dump(R,open('w13_newB.json','w'))
