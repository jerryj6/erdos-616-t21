"""Referee (n4): (a) all triple-size vectors of a K4 = 4 edges of size 21, pairwise |∩|=5, empty 4-fold ∩,
satisfying F1 (triples>=1) and L (union>=61). (b) which arise from two cross-type singles Z,Z' of a 5-pair (X,Y)
with |Z∩Z'|=5. (c) S4-orbit structure of (3,2,1,1) and its Venn region sizes."""
import itertools
E=range(4); TR=list(itertools.combinations(E,3)); PR=list(itertools.combinations(E,2))
def regions(t):  # t: dict triple->size ; returns pair-private sizes p_ij, private o_i, union
    p={pr:5-sum(t[T] for T in TR if set(pr)<=set(T)) for pr in PR}
    if min(p.values())<0: return None
    o={i:21-sum(p[pr] for pr in PR if i in pr)-sum(t[T] for T in TR if i in T) for i in E}
    if min(o.values())<0: return None
    U=sum(t.values())+sum(p.values())+sum(o.values())
    return p,o,U
feas=set()
for vals in itertools.product(range(1,6),repeat=4):
    t=dict(zip(TR,vals)); r=regions(t)
    if r is None: continue
    if r[2]>=61: feas.add(tuple(sorted(vals,reverse=True)))
print('K4 triple multisets allowed by F1+L+sizes:',sorted(feas))
# (b) from cross-type singles: triples X∩Y∩Z={y}, X∩Y∩Z'={y'}, X∩Z∩Z'=a, Y∩Z∩Z'=c, a+c=5, a,c>=1
print('from NK violations:',sorted(set(tuple(sorted((1,1,a,5-a),reverse=True)) for a in range(1,5))))
# (c) labellings of (3,2,1,1): sizes per triple; triple T is determined by the omitted edge
lab=set()
for perm in itertools.permutations([3,2,1,1]):
    t={T:perm[[i for i in E if i not in T][0]] for T in TR}
    p,o,U=regions(t)
    lab.add((tuple(sorted(t.items())),))
print('number of distinct labelled (3,2,1,1) triple assignments:',len(lab),'(=12 = 4!/2: one S4-orbit, stabiliser = swap of the two 1-omitting edges)')
t={(0,1,2):1,(0,1,3):1,(0,2,3):2,(1,2,3):3}
p,o,U=regions(t); print('w13/w8 labelling: pair-private',p,'private',o,'union',U,'core',sum(t.values())+sum(p.values()))
