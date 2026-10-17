import importlib.util,sys
src=open('w9_sclosure.py').read().split('it = 0')[0]
exec(src)
from collections import Counter
for Dt in [(0,6,7,8),(0,1,5,9),(0,5,9,10),(0,1,2,5),(5,6,9,10)]:
    D=m(*Dt); pats=status(D,good)
    cnt=Counter(); 
    for e in pats: cnt[(pc(e&Nm),pc(e&A0),pc(e&C0))]+=1
    print(Dt,len(pats),'(n,a0,c0) classes:',sorted(cnt.items())[:20])
