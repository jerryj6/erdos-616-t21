import json
from w13_enum import *
D=json.load(open('w13_dom.json'))
I={s:a for a,s in enumerate(NAMES)}
R=[('v',['v']),('w',['w']),('al',['al0','al1']),('g',['g0','g1','g2']),('m',['m0','m1','m2']),('a3',['a3_0','a3_1']),('a4',['a4_0','a4_1']),('c3',['c3']),('c4',['c4'])]
def sig(b,o): return [sum(b>>I[x]&1 for x in L) for _,L in R]+list(o)+[21-pc(b)-sum(o)]
hdr=[r for r,_ in R]+['o0','o1','o2','o3','u']
for key in ['(0,1):m0','(0,2):al0','(0,2):a3_0','(1,2):g0','(1,2):c3','(2,3):al0','(2,3):g0']:
    S=[sig(b,o) for b,o in D[key]]
    print(f'{key:11s}',' '.join(f'{h}[{min(s[k] for s in S)}-{max(s[k] for s in S)}]' for k,h in enumerate(hdr)), ' v+w', sorted(set(s[0]+s[1] for s in S)), ' al+a3', sorted(set(s[2]+s[5] for s in S)),' g+c3+c4',sorted(set(s[3]+s[7]+s[8] for s in S)))
