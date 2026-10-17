import itertools as it, math
print('LemmaA m=5..17:', [(m, 42-m+math.ceil(m/4)*(17-m)) for m in range(5,18)])
# Kneser K(9,4) connectivity (independent BFS on 4-subsets, adjacency = disjoint)
def kneser_conn(n,k):
    V=[frozenset(s) for s in it.combinations(range(n),k)]; seen={V[0]}; st=[V[0]]
    while st:
        a=st.pop()
        for b in V:
            if not a&b and b not in seen: seen.add(b); st.append(b)
    return len(seen),len(V)
print('K(9,4) reach', kneser_conn(9,4), ' K(13,4) reach (=closure on complements)', kneser_conn(13,4))
# W6-U final family, recomputed from scratch: 4-sets C_i={s0}uR_i; B_i=S\C_i
S=set(range(13)); Rs=[{1,2,3},{4,5,6},{7,8,9},{10,11,12}]; B=[S-({0}|R) for R in Rs]
print('W6-U family: |cap B|=',len(set.intersection(*B)),'|cup B|=',len(set.union(*B)),'span',len(set.union(*B))+4*12)
# Step 4 independent: enumerate U_k (3-subsets of Q_a u Q_b), test (star) for all ordered (k,a,b)
Q={1:{3,4,5},2:{6,7,8},3:{9,10,11}}; cnt=0; tot=0
for U in it.product(*[[set(s) for s in it.combinations(sorted(set().union(*[Q[j] for j in Q if j!=k])),3)] for k in (1,2,3)]):
    U=dict(zip((1,2,3),U)); tot+=1
    if all(not(len(U[k]&Q[a])<=2) or (U[k]&Q[b])<=(U[a]&Q[b]) for k,a,b in it.permutations((1,2,3))): cnt+=1
print('Step4 cases',tot,'satisfying star',cnt)
