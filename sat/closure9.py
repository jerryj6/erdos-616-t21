# Uniform |S|=9 closure: F contains A; for B in F with known partner D_B (= S1\B for any S1 in F, |S1&B|=5),
# F contains (B\C)|D_B for all 4-subsets C of B.
from itertools import combinations
A = frozenset(range(9)); D = frozenset(range(9,13))
F = {A: D}
frontier = [A]
while frontier:
    nf = []
    for B in frontier:
        DB = F[B]
        for C in combinations(sorted(B), 4):
            S = (B - set(C)) | DB
            if S not in F:
                F[S] = frozenset(C)   # partner of S is C (since B in F, B\S = C, |B&S|=5)
                nf.append(S)
            else:
                assert F[S] == frozenset(C), "partner inconsistency -> contradiction already"
    frontier = nf
print(len(F), all(len(s)==9 and s <= A|D for s in F))
# check: contains violating 4-family for r=21: complements in Y {x}+4 disjoint triples
Y = A|D
Ts = {Y - s for s in F}
viol = None
x=0; rest=list(range(1,13))
fam=[frozenset({0,1,2,3}),frozenset({0,4,5,6}),frozenset({0,7,8,9}),frozenset({0,10,11,12})]
print(all(t in Ts for t in fam))
