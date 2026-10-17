import json, itertools, collections
from w13_enum import *
from w13_tau import orbit
feas=json.load(open('w13_feas.json'))
def states(b):
    L=[max(0,5-pc(b&P[i])) for i in range(4)]
    for d in itertools.product(range(3),repeat=4):
        o=[L[i]+d[i] for i in range(4)]
        if any(o[i]>OSZ[i] for i in range(4)) or sum(o)+pc(b)>21: continue
        if not check(b,o): yield o
FS={b:list(states(b)) for b in feas}
print('states',sum(len(v) for v in FS.values()),flush=True)
def l3slack(b,o,B):
    s=0;k=0
    for T,t in TRI.items():
        if t & ~B: continue   # triple not fully avoided
        k+=1
        s+=8+pc(t)-(pc(b&(P[T[0]]|P[T[1]]|P[T[2]]))+sum(o[q] for q in T))
    return k,s
R=[];seen=set()
for Bt in itertools.combinations(range(n),4):
    B=sum(1<<a for a in Bt)
    if B in seen: continue
    orb=orbit(B); seen|=orb
    if not all(B&P[i] for i in range(4)): continue
    sl=[];
    for b in feas:
        if b&B: continue
        for o in FS[b]:
            k,s=l3slack(b,o,B); sl.append(s)
    if k==0: continue
    R.append((k,max(sl),collections.Counter(sl).most_common(4),len(sl),nm(B),len(orb)))
R.sort(key=lambda r:(r[1]-0*r[0],-r[0]))
for r in R: print(r)
json.dump(R,open('w13_squeeze.json','w'))
