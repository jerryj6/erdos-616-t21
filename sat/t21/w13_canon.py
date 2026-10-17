import json, itertools, collections, sys
from w13_enum import *
feas=json.load(open('w13_feas.json'))
I={s:a for a,s in enumerate(NAMES)}
R=[('v',['v']),('w',['w']),('al',['al0','al1']),('g',['g0','g1','g2']),('m',['m0','m1','m2']),('a3',['a3_0','a3_1']),('a4',['a4_0','a4_1']),('c3',['c3']),('c4',['c4'])]
def full_states(b):
    L=[max(0,5-pc(b&P[i])) for i in range(4)]
    for d in itertools.product(range(4),repeat=4):
        o=[L[i]+d[i] for i in range(4)]
        if any(o[i]>OSZ[i] for i in range(4)) or sum(o)+pc(b)>21: continue
        if not check(b,o): yield o
for Bn in sys.argv[1:]:
    B=sum(1<<I[x] for x in Bn.split(','))
    C=collections.Counter(); P5=collections.Counter()
    for b in feas:
        if b&B: continue
        for o in full_states(b):
            s=tuple(sum(b>>I[x]&1 for x in L) for _,L in R)+tuple(o)
            C[s]+=1
            P5[tuple(pc(b&P[i])+o[i] for i in range(4))]+=1
    print('B=',Bn,'region signatures',len(C))
    keys=[r for r,_ in R]+['o0','o1','o2','o3']
    for k,h in enumerate(keys): print(f'  {h}:{sorted(set(s[k] for s in C))}',end='')
    print('\n  |J&P_i| vectors:',sorted(P5.items()))
