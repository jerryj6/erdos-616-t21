"""Referee (n4): first-generation slot lists of the noK4 encodings vs. the base (own recomputation of gen-1 singles)."""
import itertools, json, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 't21'))
from w9lazy import base_nok4
def gen1(B):
    out=[]
    for i,j in itertools.combinations(range(4),2):
        N=B[i]&B[j]
        if len(N)!=5: continue
        for y in sorted(N):
            if any(len(B[k]&N)==1 and y in B[k] for k in range(4) if k not in (i,j)): continue
            out.append(frozenset(N-{y}))
    return out
for a,c in [(2,4),(3,3),(3,4)]:
    nm,B=base_nok4(a,c); g=gen1(B)
    fp=[(i,j) for i,j in itertools.combinations(range(4),2) if len(B[i]&B[j])==5]
    print((a,c),'base 5-pairs',fp,'gen1 singles',len(g),[sorted(nm[x] for x in s) for s in g[:3]],'...')
    if (a,c)==(2,4):
        d=json.load(open('../t21/w9_cn24.json')); E=d['edges'][:24]
        av=[frozenset(e['avoid']) for e in E]
        print('  w9_cn24 first 19 == gen1 set:',set(av[:19])==set(g),' len',len(set(av[:19])))
        for e in E[19:]: print('  generic slot avoid',sorted(nm[x] for x in e['avoid']))
