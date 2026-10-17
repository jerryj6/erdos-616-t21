import json, itertools, collections
from w13_enum import NAMES, W8
ren=dict(zip(W8,NAMES))
def load(f):
    d=json.load(open(f)); names=d.get('names') or d.get('named')
    E=[]
    for e in d['edges']:
        E.append(frozenset((names[x] if x<len(names) else f'u{x}') if isinstance(x,int) else x for x in e))
    E=[frozenset(ren.get(p,p) for p in e) for e in E]
    return d['labels'],E
for f in ['w12_M10_real_keep.json','w11_B_real_keep.json','w10x_w12Br2_real.json']:
    labs,E=load(f); pts=sorted(set().union(*E),key=str)
    for t in (1,2,3):
        T=[S for S in itertools.combinations(pts,t) if all(e&set(S) for e in E)]
        if T: break
    print(f,'edges',len(E),'tau',t,'#min',len(T)); print('  ',T[:30])
    for l,e in zip(labs,E):
        print('   ',l, sorted(p for p in e if p in NAMES), {k:sum(1 for p in e if str(p).startswith(k)) for k in ('O0','O1','O2','O3')}, 'U',sum(1 for p in e if str(p) not in NAMES and not str(p).startswith('O')))
