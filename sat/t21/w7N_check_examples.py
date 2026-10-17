"""Wave 7 Case N: literal checks on H(16,10,7) (r=16,K=4) and H(22,13,9) (r=22,K=5) of the trace-system facts
T1 (traces E1&X of K-pair partners X pairwise intersect), T2 (every trace has a tangent trace at each of its
points), T3 (no triangle of traces), and absence of K4 configurations (4 edges pairwise meeting in exactly K)."""
import itertools
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
for (r, k, q, K) in [(16, 10, 7, 4), (22, 13, 9, 5)]:
    E = H(r, k, q); E1 = E[0]
    tr = sorted({E1 & X for X in E[1:] if len(E1 & X) == K}, key=sorted)
    T1 = all(a & b for a, b in itertools.combinations(tr, 2))
    T2 = all(any(s & t == {x} for t in tr) for s in tr for x in s)
    T3 = not any(len(a & b) == 1 and len(b & c) == 1 and len(a & c) == 1 and not (a & b & c)
                 for a, b, c in itertools.combinations(tr, 3))
    tang_equal = all((t1 - {x}) == (t2 - {y}) for s in tr for x, y in itertools.permutations(s, 2)
                     for t1 in tr if s & t1 == {x} for t2 in tr if s & t2 == {y})
    # K4: search among edges pairwise meeting in exactly K (cliques of size 4 in the K-graph through E[0])
    nb = [i for i in range(1, len(E)) if len(E[0] & E[i]) == K]
    k4 = any(len(E[i] & E[j]) == K and len(E[i] & E[l]) == K and len(E[j] & E[l]) == K and not (E[0] & E[i] & E[j] & E[l])
             for i, j, l in itertools.combinations(nb, 3))
    print(f'r={r}: traces={len(tr)} T1={T1} T2={T2} T3={T3} tangents-uniform={tang_equal} K4-through-E0={k4}')
