import json, itertools, time
from w13_enum import *
S = json.load(open('w13_singles.json'))
def all_o_single(b,i,j):
    o=[None]*4
    o[i]=5-pc(b&P[i]); o[j]=5-pc(b&P[j])
    if o[i]<0 or o[j]<0 or o[i]>OSZ[i] or o[j]>OSZ[j]: return []
    k,l=[q for q in range(4) if q not in (i,j)]
    out=[]
    for ok in range(OSZ[k]+1):
        for ol in range(OSZ[l]+1):
            o[k]=ok;o[l]=ol
            if pc(b)+sum(o)>21: break
            if not check(b,o): out.append(tuple(o))
    return out
D={}
t=time.time()
for key,L in S.items():
    i,j=int(key[1]),int(key[3])
    D[key]=[(b,o) for b in L for o in all_o_single(b,i,j)]
    print(key,len(L),len(D[key]),round(time.time()-t))
json.dump({k:[[b,list(o)] for b,o in v] for k,v in D.items()},open('w13_dom.json','w'))
