#!/usr/bin/env python3
"""cmp.py ORIG.cnf LEAN.dimacs : compare clause sequences (ignoring comments/header/whitespace)."""
import sys
def clauses(p):
    out=[]; cur=[]
    with open(p) as f:
        for line in f:
            s=line.strip()
            if not s or s[0] in 'cp%': continue
            for t in s.split():
                v=int(t)
                if v==0: out.append(tuple(cur)); cur=[]
                else: cur.append(v)
    return out
a=clauses(sys.argv[1]); b=clauses(sys.argv[2])
print('clauses', len(a), len(b), 'IDENTICAL' if a==b else 'DIFFER')
