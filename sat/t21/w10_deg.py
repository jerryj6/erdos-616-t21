"""Wave 10: pairwise U-overlap bounds and the degree count for a stall core (diagnostic).
ub(F,G) = min over base subfamilies B' with (cap B') & b_F & b_G = {} of  c_F + c_G - (61 - |cup B' u b_F u b_G|)
         (L on B' u {F,G} + |F|=21; for |B'|=2 a 5-pair this is exactly OO).  lb(F,G) = 5 - |b_F & b_G| (Lemma A).
compat(F,G) iff ub >= 1 (they CAN share an outside point).  omega_F = max clique of compat containing F.
Degree count (sound for this core): sum_G lb(F,G)^+ <= (omega_F - 1) * c_F."""
import sys, json, itertools
d = json.load(open(sys.argv[1])); base=[frozenset(b) for b in d['base']]; new=[frozenset(e['pts']) for e in d['edges']]
lab=[e['label'] for e in d['edges']]; n=len(new); c=[21-len(b) for b in new]
def ub(F,G):
    best=min(c[F],c[G])
    for k in range(1,5):
        for Bp in itertools.combinations(range(4),k):
            I=frozenset.intersection(*[base[i] for i in Bp])&new[F]&new[G]
            if I: continue
            U=frozenset.union(*[base[i] for i in Bp])|new[F]|new[G]
            best=min(best, c[F]+c[G]-(61-len(U)))
    return best
UB={}; LB={}
for F,G in itertools.combinations(range(n),2):
    UB[F,G]=UB[G,F]=ub(F,G); LB[F,G]=LB[G,F]=max(0,5-len(new[F]&new[G]))
bad=[(lab[F],lab[G],LB[F,G],UB[F,G]) for F,G in itertools.combinations(range(n),2) if LB[F,G]>UB[F,G]]
print('pairwise lb>ub:',len(bad),bad[:5])
comp={F:{G for G in range(n) if G!=F and UB[F,G]>=1} for F in range(n)}
def maxclique(R,P,X,best):
    if not P and not X: return max(best,len(R))
    for v in list(P):
        best=maxclique(R|{v},P&comp[v],X&comp[v],best); P=P-{v}; X=X|{v}
    return best
tot=0
for F in range(n):
    w=maxclique({F},set(comp[F]),set(),0); dem=sum(LB[F,G] for G in range(n) if G!=F)
    print(f'{lab[F]:28s} cap={c[F]:2d} demand={dem:2d} compat={len(comp[F]):2d} omega={w:2d} bound={(w-1)*c[F]:3d}', 'VIOL' if dem>(w-1)*c[F] else '')
