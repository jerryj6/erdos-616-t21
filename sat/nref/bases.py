"""Referee (n4): the base configurations of the encodings vs. the configuration forced by the leaf hypotheses.
Generic(a,c): 5-pair (E1,E2), M=E1∩E2, G single type v, H single type w≠v, |A_G|=|C_G|=|A_H|=|C_H|=4, |O|=12 (R.3),
O_G∩O_H=∅ (S(a)), |A_G∩A_H|=a, |C_G∩C_H|=c.  Built independently (own point labels)."""
import itertools, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 't21'))
def generic(a,c):
    pts=iter(range(1000)); nx=lambda k:[next(pts) for _ in range(k)]
    M=nx(5); v,w=M[0],M[1]
    A=nx(16); C=nx(16)
    AG=A[:4]; AH=A[4-a:8-a]; CG=C[:4]; CH=C[4-c:8-c]
    OG=nx(12); OH=nx(12)
    E1=set(M+A); E2=set(M+C); G={v}|set(AG+CG+OG); H={w}|set(AH+CH+OH)
    return [E1,E2,G,H]
def venn(F):
    pts=set().union(*F); cnt={}
    for x in pts:
        k=frozenset(i for i in range(4) if x in F[i]); cnt[k]=cnt.get(k,0)+1
    return cnt
def iso(F1,F2):
    v1=venn(F1); v2=venn(F2)
    for pm in itertools.permutations(range(4)):
        if all(v2.get(frozenset(pm[i] for i in k),0)==n for k,n in v1.items()) and sum(v1.values())==sum(v2.values()):
            return pm
    return None
def stats(F):
    return [len(F[i]&F[j]) for i,j in itertools.combinations(range(4),2)],[len(F[i]&F[j]&F[k]) for i,j,k in itertools.combinations(range(4),3)],len(F[0]&F[1]&F[2]&F[3]),len(set().union(*F))
from w9lazy import base_nok4
ok=True
for a,c in [(2,4),(4,2),(3,3),(3,4),(4,3),(2,3),(3,2)]:
    Fg=generic(a,c); print((a,c),'generic pairs/triples/quad/union',stats(Fg))
    if (a,c) in [(2,4),(3,3),(3,4)]:
        nm,B=base_nok4(a,c); B=[set(x) for x in B]
        # identity-labelled check: E1=B0,E2=B1,G=B2,H=B3 ; and G,H singles of (B0,B1) of types v,w with class (a,c)
        M=B[0]&B[1]; aa=len(B[2]&B[3]&(B[0]-M)); cc=len(B[2]&B[3]&(B[1]-M))
        same = venn(Fg)==venn(B)
        print('   base_nok4: |M|',len(M),'G∩M',[nm[x] for x in B[2]&M],'H∩M',[nm[x] for x in B[3]&M],'class',(aa,cc),'Venn identical (no relabel):',same)
        ok&=same and (aa,cc)==(a,c)
# (4,2),(4,3) = (2,4),(3,4) with E1<->E2
for (a,c),(b,d) in [((4,2),(2,4)),((4,3),(3,4))]:
    pm=iso(generic(a,c),generic(b,d)); print((a,c),'->',(b,d),'isomorphism (edge perm)',pm); ok&=pm==(1,0,2,3)
# K4 base used by w13/w14 (MEM) and w8k4 PAT 3211
from w13_enum import MEM,OSZ
K=[set() for _ in range(4)]; nxt=0
for m in MEM:
    for i in m: K[i].add(nxt)
    nxt+=1
for i in range(4):
    for _ in range(OSZ[i]): K[i].add(nxt); nxt+=1
print('w13 K4 base',stats(K))
from w9lazy import base_k4
nm,BK=base_k4('3211'); BK=[set(x) for x in BK]; print('w8/w9 base_k4(3211)',stats(BK),'Venn==w13:',venn(BK)==venn(K))
for a,c in [(2,3),(3,2)]:
    pm=iso(generic(a,c),K); print((a,c),'generic NK-violation K4 -> w13 base via edge perm',pm); ok&=pm is not None
# N.4 witness K4: {E1,G,E2,W}, W single of (E1,G) of type p, k=|W∩M|, c'=|W∩C_G|, k+c'=5
def witnessK4(k):
    E1,E2,G,H=generic(4,4); M=sorted(E1&E2); v=M[0]
    AG=sorted((G&E1)-{v}); CG=sorted((G&E2)-{v}); p=AG[0]
    Arest=sorted(E1-set(M)-set(AG)); Grest=sorted(G-E1-E2)
    W={p}|set(M[1:1+k])|set(Arest[:4-k])|set(CG[:5-k])|set(Grest[:4-(5-k)])
    W|=set(range(5000,5000+21-len(W)))
    return [E1,E2,G,W]
for k in (2,3):
    F=witnessK4(k); print('N.4 witness K4 k=',k,stats(F),'iso to w13 base:',iso(F,K))
    ok&=iso(F,K) is not None
print('ALL OK' if ok else 'MISMATCH')
