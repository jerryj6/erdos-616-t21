import json, itertools, collections
from w13_enum import *
from w13_tau import orbit
from w13_canon import R, I
feas=json.load(open('w13_feas.json'))
def states(b):
    L=[max(0,5-pc(b&P[i])) for i in range(4)]
    for d in itertools.product(range(3),repeat=4):
        o=[L[i]+d[i] for i in range(4)]
        if any(o[i]>OSZ[i] for i in range(4)) or sum(o)+pc(b)>21: continue
        if not check(b,o): yield tuple(o)
FS={b:list(states(b)) for b in feas}
def firstgen(b):
    out=[]
    for (i,j),Nij in N.items():
        s=b&Nij
        if pc(s)==1 and not any(base_single(k,i,j)==s for k in range(4) if k not in (i,j)): out.append(f'{i}{j}')
    return out
out=[];seen=set()
for Bt in itertools.combinations(range(n),4):
    B=sum(1<<a for a in Bt)
    if B in seen: continue
    orb=orbit(B); seen|=orb
    if not all(B&P[i] for i in range(4)): continue
    sig=set(); nonfg=0; tot=0; p5=collections.Counter()
    for b in feas:
        if b&B: continue
        fg=firstgen(b)
        for o in FS[b]:
            tot+=1
            sig.add(tuple(sum(b>>I[x]&1 for x in L) for _,L in R)+o)
            if not fg: nonfg+=1
            p5[sum(1 for i in range(4) if pc(b&P[i])+o[i]==5)]+=1
    always_fg = (nonfg==0)
    out.append(dict(B=nm(B),orbit=len(orb),nsig=len(sig),states=tot,nonfirstgen=nonfg,always_firstgen=always_fg,num5pairs_with_base=dict(sorted(p5.items()))))
out.sort(key=lambda r:(r['always_firstgen'], r['nsig']))
json.dump(out,open('w13_rigid.json','w'),indent=0)
for r in out[:45]: print(r)
