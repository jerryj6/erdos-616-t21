"""Order-576 automorphism group of the (3,2,1,1)-K4 base on the 16 core points (with the induced P-index map).
An element is (perm of 16 core points, perm of base indices). Validity is CHECKED: g maps P_i&core onto P_pi(i)&core
and OSZ[pi(i)] = OSZ[i]; then every rule written in terms of P, N, TRI, OSZ is invariant."""
import sys, itertools
sys.path.insert(0, '..')
from w13_enum import NAMES, P, OSZ, n
I = {s: a for a, s in enumerate(NAMES)}
def tr(x, y):
    p = list(range(n)); p[I[x]], p[I[y]] = I[y], I[x]; return (tuple(p), (0, 1, 2, 3))
sig = list(range(n))
for x, y in [('v','w'),('a3_0','a4_0'),('a3_1','a4_1'),('c3','c4')]:
    sig[I[x]], sig[I[y]] = I[y], I[x]
gens = [tr('al0','al1'), tr('g0','g1'), tr('g1','g2'), tr('m0','m1'), tr('m1','m2'), tr('a3_0','a3_1'), tr('a4_0','a4_1'),
        (tuple(sig), (0, 1, 3, 2))]
def app(p, x):
    y = 0
    for a in range(n):
        if x >> a & 1: y |= 1 << p[a]
    return y
def comp(g, h):  # g after h
    return (tuple(g[0][h[0][a]] for a in range(n)), tuple(g[1][h[1][i]] for i in range(4)))
def elements():
    e = (tuple(range(n)), (0, 1, 2, 3)); G = {e}; st = [e]
    while st:
        x = st.pop()
        for g in gens:
            y = comp(g, x)
            if y not in G: G.add(y); st.append(y)
    return sorted(G)
G = elements()
for p, pi in G:
    for i in range(4):
        assert app(p, P[i]) == P[pi[i]] and OSZ[pi[i]] == OSZ[i]
if __name__ == '__main__': print('group order', len(G), 'valid')
