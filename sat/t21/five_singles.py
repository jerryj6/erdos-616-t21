# Case N feasibility of the 5 singles' (A,C)-parts at r=21 (necessary conditions only)
import itertools, sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
NP=16
def run(a0,c0):
    pool=IDPool(); cl=[]
    A=[[pool.id(('A',i,p)) for p in range(NP)] for i in range(5)]
    C=[[pool.id(('C',i,p)) for p in range(NP)] for i in range(5)]
    def card_eq(lits,k):
        e=CardEnc.equals(lits=lits,bound=k,vpool=pool,encoding=EncType.seqcounter); cl.extend(e.clauses)
    for i in range(5): card_eq(A[i],4); card_eq(C[i],4)
    def inter(X,i,j):
        v=[]
        for p in range(NP):
            t=pool.id(('t',id(X),i,j,p)); cl.append([-t,X[i][p]]); cl.append([-t,X[j][p]]); cl.append([t,-X[i][p],-X[j][p]]); v.append(t)
        return v
    def atleast(l,k):
        e=CardEnc.atleast(lits=l,bound=k,vpool=pool,encoding=EncType.seqcounter); cl.extend(e.clauses)
    ia={};ic={}
    for i,j in itertools.combinations(range(5),2):
        ia[i,j]=inter(A,i,j); ic[i,j]=inter(C,i,j)
        cl.append(list(ia[i,j])); cl.append(list(ic[i,j]))
        atleast(ia[i,j]+ic[i,j],5)
        # a=1 => C equal ; c=1 => A equal
        # a<=1 means: not (at least 2) ; encode: at least2(ia) or C_i==C_j
        a2=pool.id(('a2',i,j)); c2=pool.id(('c2',i,j))
        e=CardEnc.atleast(lits=ia[i,j],bound=2,vpool=pool,encoding=EncType.seqcounter)
        # a2 <-> atleast2 : only need a2 -> atleast2 direction and (not a2 -> C equal)
        for c in e.clauses: cl.append([-a2]+c)
        e=CardEnc.atleast(lits=ic[i,j],bound=2,vpool=pool,encoding=EncType.seqcounter)
        for c in e.clauses: cl.append([-c2]+c)
        for p in range(NP):
            cl.append([a2,-C[i][p],C[j][p]]); cl.append([a2,C[i][p],-C[j][p]])
            cl.append([c2,-A[i][p],A[j][p]]); cl.append([c2,A[i][p],-A[j][p]])
    for k in (3,4):
        for S in itertools.combinations(range(5),k):
            common=[]
            for X in (A,C):
                for p in range(NP):
                    t=pool.id(('cm',id(X),S,p)); cl.append([-t]+[X[i][p] for i in S][:1]); 
                    for i in S: cl.append([-t,X[i][p]])
                    common.append(t)
            if k==3: cl.append(common)
            else:
                # common OR |unionA|+|unionC|>=9
                g=pool.id(('g',S)); 
                cl.append(common+[g])
                un=[]
                for X in (A,C):
                    for p in range(NP):
                        u=pool.id(('u',id(X),S,p)); 
                        for i in S: cl.append([-X[i][p],u])
                        cl.append([-u]+[X[i][p] for i in S]); un.append(u)
                e=CardEnc.atleast(lits=un,bound=9,vpool=pool,encoding=EncType.seqcounter)
                for c in e.clauses: cl.append([-g]+c)
    # pair (0,1) exactly (a0,c0)
    for lits,k in ((ia[0,1],a0),(ic[0,1],c0)): card_eq(lits,k)
    # symmetry: A_0 = {0..3}, C_0={0..3}
    for p in range(NP):
        cl.append([A[0][p] if p<4 else -A[0][p]]); cl.append([C[0][p] if p<4 else -C[0][p]])
    s=Cadical153(bootstrap_with=cl); r=s.solve()
    print(a0,c0,'SAT' if r else 'UNSAT',flush=True)
    if r:
        m=set(x for x in s.get_model() if x>0)
        for i in range(5): print(i,[p for p in range(NP) if A[i][p] in m],[p for p in range(NP) if C[i][p] in m])
for a0,c0 in [(2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3)]: run(a0,c0)
