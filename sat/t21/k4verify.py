"""Verify the K4 configuration claim (06:14 run) concretely: build E1=M+A, E2=M+C, G (type v), H (type w) with
|A_G&A_H|=a, |C_G&C_H|=c, O_G, O_H disjoint 12-sets (Lemma R.3/S(a)); print pairwise/triple sizes and union."""
import itertools
for a, c in [(2,3),(3,2),(2,4),(4,2),(3,3),(3,4),(4,3),(1,4)]:
    M = list(range(5)); A = list(range(5,21)); C = list(range(21,37))
    E1, E2 = set(M+A), set(M+C)
    G = {0} | set(A[0:4]) | set(C[0:4]) | set(range(100,112))
    H = {1} | set(A[4-a:8-a]) | set(C[4-c:8-c]) | set(range(200,212))
    F = [E1,E2,G,H]; assert all(len(X)==21 for X in F)
    pr = [len(F[i]&F[j]) for i,j in itertools.combinations(range(4),2)]
    tr = [len(F[i]&F[j]&F[k]) for i,j,k in itertools.combinations(range(4),3)]
    print((a,c), 'pairs', pr, 'triples', tr, 'quad', len(E1&E2&G&H), 'union', len(E1|E2|G|H))
