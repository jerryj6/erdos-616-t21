import json, itertools, collections
from w13_enum import *
from w13_tau import orbit
from w13_real import load
FILES=['w12_M10_real_keep.json','w10x_w12m1_real.json','w11_B_real_keep.json','w10x_w12b1_real.json','w10x_w12Br1_real.json','w10x_w12Br2_real.json','w10x_w12Pr0_real.json','w10x_w12Pr1_real.json']
I={s:a for a,s in enumerate(NAMES)}
reals=[]
for f in FILES:
    try: labs,E=load(f)
    except Exception as e: print('skip',f,e); continue
    tr=[sum(1<<I[p] for p in e if p in I) for e in E]
    reals.append((f,labs,tr))
    print(f, len(E), 'edges; labels', [l.split(':')[-1] if ':' in l else l for l in labs][4:])
seen=set(); R=[]
for Bt in itertools.combinations(range(n),4):
    B=sum(1<<a for a in Bt)
    if B in seen: continue
    orb=orbit(B); seen|=orb
    if not all(B&P[i] for i in range(4)): continue
    row=[]
    for f,labs,tr in reals:
        k=sum(1 for X in orb if all(t&X for t in tr))
        row.append(k)
    R.append((nm(B),len(orb),row, sum(1 for k in row if k>0)))
R.sort(key=lambda r:(-r[3], r[1]))
print('orbit rep | orbit size | #images that are transversals, per realization | #realizations hit')
for r in R[:40]: print(r)
json.dump(R,open('w13_realtrans.json','w'))
