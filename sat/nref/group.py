"""Referee (n4): automorphism group order of the labelled (3,2,1,1) core (16 core points, MEM of w13_enum) and the
stabiliser of B*={w}∪γ; check every base edge meets B*."""
import itertools, sys, math, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 't21'))
from w13_enum import MEM, OSZ, NAMES
reg={}
for a,m in enumerate(MEM): reg.setdefault(frozenset(m),[]).append(a)
good=[]
for pm in itertools.permutations(range(4)):
    if all(len(reg.get(frozenset(pm[i] for i in k),[]))==len(v) for k,v in reg.items()) and all(OSZ[pm[i]]==OSZ[i] for i in range(4)):
        good.append(pm)
inner=math.prod(math.factorial(len(v)) for v in reg.values())
print('edge perms preserving Venn+OSZ:',good,' |Aut core| =',len(good)*inner)
Bs={NAMES.index(x) for x in ['w','g0','g1','g2']}
print('each base edge meets B*:',[bool(Bs & {a for a,m in enumerate(MEM) if i in m}) for i in range(4)])
# stabiliser of B*: edge perm must map {w}∪γ to itself; swap(2,3) maps w(T013)->T012=v, so only identity
stab=[pm for pm in good if {frozenset(pm[i] for i in MEM[a]) for a in Bs}=={frozenset(MEM[a]) for a in Bs}]
print('edge perms stabilising B* region-wise:',stab,' |Stab|=',len(stab)*inner)
