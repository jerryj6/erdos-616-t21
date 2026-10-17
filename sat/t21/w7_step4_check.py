# Brute-force sanity check of Step 4 (§7.4): no triple (U1,U2,U3), U_k a 3-subset of Q_a u Q_b, satisfies
# (star): |U_k & Q_a| <= 2  =>  U_k & Q_b  subset of  U_a & Q_b   for all distinct a,b,k.
from itertools import combinations, permutations
Q = {1: {3,4,5}, 2: {6,7,8}, 3: {9,10,11}}
opts = {k: [frozenset(s) for s in combinations(sorted(set().union(*[Q[i] for i in Q if i != k])), 3)] for k in Q}
bad = 0
for U1 in opts[1]:
    for U2 in opts[2]:
        for U3 in opts[3]:
            U = {1: U1, 2: U2, 3: U3}; ok = True
            for k, a, b in permutations((1,2,3)):
                if len(U[k] & Q[a]) <= 2 and not (U[k] & Q[b]) <= (U[a] & Q[b]): ok = False; break
            bad += ok
print('assignments satisfying (star):', bad)
