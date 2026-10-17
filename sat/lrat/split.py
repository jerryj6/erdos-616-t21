#!/usr/bin/env python3
"""split.py NAME NCLAUSES BUDGET_MB : split renumbered lrat/NAME.lrat into blocks chunks/NAME/lem_j.cnf + hints_j.txt.
Drops deletions; refuses RAT (negative hints); checks lemma ids are contiguous from NCLAUSES+1. Untrusted."""
import sys, os
name, m, budget = sys.argv[1], int(sys.argv[2]), int(float(sys.argv[3])*1e6)
d=f'chunks/{name}'; os.makedirs(d, exist_ok=True)
j=0; size=0; nxt=m+1
lf=open(f'{d}/lem_{j}.cnf','w'); hf=open(f'{d}/hints_{j}.txt','w'); nlem=[0]
done=False
with open(f'lrat/{name}.lrat') as f:
    for line in f:
        t=line.split()
        if not t or t[1]=='d': continue
        assert not done, 'lines after empty clause'
        i=int(t[0]); z=t.index('0',1); lits=t[1:z]; hints=t[z+1:-1]
        assert t[-1]=='0'
        assert all(not h.startswith('-') for h in hints), 'RAT hint'
        if size>budget and lits:
            lf.close(); hf.close(); j+=1; size=0; nlem.append(0)
            lf=open(f'{d}/lem_{j}.cnf','w'); hf=open(f'{d}/hints_{j}.txt','w')
        if lits:
            assert i==nxt, (i,nxt); nxt+=1
        else:
            done=True
        s=f"{i} 0 "+' '.join(hints)+' 0\n'
        lf.write(' '.join(lits+['0'])+'\n'); hf.write(s); size+=len(s); nlem[-1]+=1
lf.close(); hf.close()
assert done, 'no empty clause'
print('blocks', j+1, 'lemmas per block', nlem)
