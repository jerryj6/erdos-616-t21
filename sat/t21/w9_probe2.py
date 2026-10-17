src=open('w9_sclosure.py').read().split('it = 0')[0]
exec(src)
import itertools
mn=10**9; full_ok=0; tot=0
for Dt in itertools.combinations(range(13),4):
    D=m(*Dt)
    if D in set(good): continue
    pats=status(D,good); tot+=1
    mn=min(mn,len(pats)); full_ok+= (S&~D) in pats
print('NK',NK,'4-sets',tot,'min #surviving patterns',mn,'full pattern feasible for',full_ok)
