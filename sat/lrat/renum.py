#!/usr/bin/env python3
"""renum.py NCLAUSES IN.lrat OUT.lrat : renumber LRAT lemma ids to be contiguous (NCLAUSES+1, +2, ...),
as Lean core's LRAT checker indexes clauses by position. Untrusted preprocessing (a wrong renumbering can only make
the verified checker reject)."""
import sys
m=int(sys.argv[1]); nxt=m+1; mp={}
def f(t):
    v=int(t)
    if v<0: return '-'+str(mp.get(-v,-v))
    return str(mp.get(v,v))
with open(sys.argv[2]) as fi, open(sys.argv[3],'w') as fo:
    for line in fi:
        t=line.split()
        if not t: continue
        if t[1]=='d':
            fo.write(str(nxt-1)+' d '+' '.join(f(x) for x in t[2:])+'\n')
            continue
        i=int(t[0]); z=t.index('0',1)
        lits=t[1:z]; hints=t[z+1:]
        if lits:  # non-empty lemma gets a fresh contiguous id
            mp[i]=nxt; nid=nxt; nxt+=1
        else:
            nid=nxt
        fo.write(str(nid)+' '+' '.join(lits+['0']+[f(x) for x in hints])+'\n')
