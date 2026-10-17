"""symmetry of the labelled (a,c) base: generators as (core point permutation, base-edge permutation).
Each generator is checked to map every base edge's core part onto the image edge's core part and |O_q| to |O_g(q)|,
so it extends to a point relabelling of the 61-point base fixing the base FAMILY. Applying it to a counterexample gives a
counterexample on the same base, so (semantic WLOG) Φ∧x_t SAT ⇒ Φ∧x_{g t} SAT. Also checks (sanity, not needed for the
argument) that the universe and the full conflict matrix are invariant.  usage: python3 tr_sym.py TAG [check]"""
import sys, glob, itertools, numpy as np
from tr_core import base
def gens(a, c):
    names, P, OS = base(a, c); ix = {nm: i for i, nm in enumerate(names)}
    G = []
    def perm(cyc, bp=(0, 1, 2, 3)):
        p = list(range(len(names)))
        for cy in cyc:
            for k in range(len(cy)): p[ix[cy[k]]] = ix[cy[(k + 1) % len(cy)]]
        return (p, list(bp))
    G.append(perm([('m0', 'm1')])); G.append(perm([('m0', 'm1', 'm2')]))
    if a >= 2: G.append(perm([('al0', 'al1')]))
    if a >= 3: G.append(perm([tuple(f'al{i}' for i in range(a))]))
    if c >= 2: G.append(perm([('cl0', 'cl1')]))
    if c >= 3: G.append(perm([tuple(f'cl{i}' for i in range(c))]))
    if 4 - a >= 2: G.append(perm([('ag0', 'ag1')], )); G.append(perm([('ah0', 'ah1')]))
    if 4 - c >= 2: G.append(perm([('cg0', 'cg1')])); G.append(perm([('ch0', 'ch1')]))
    G.append(perm([('v', 'w')] + [(f'ag{i}', f'ah{i}') for i in range(4 - a)] + [(f'cg{i}', f'ch{i}') for i in range(4 - c)], (0, 1, 3, 2)))
    if a == c:
        G.append(perm([(f'al{i}', f'cl{i}') for i in range(a)] + [(f'ag{i}', f'cg{i}') for i in range(4 - a)] +
                      [(f'ah{i}', f'ch{i}') for i in range(4 - a)], (1, 0, 2, 3)))
    for p, bp in G:   # check: g(P_q core) = P_{bp[q]} core, |O_q| = |O_bp[q]|
        for q in range(4):
            img = sum(1 << p[x] for x in range(len(names)) if P[q] >> x & 1)
            assert img == P[bp[q]] and OS[q] == OS[bp[q]], (p, bp, q)
    return names, P, OS, G
def apply(p, b):
    return sum(1 << p[x] for x in range(len(p)) if b >> x & 1)
def group(G, n):
    idp = tuple(range(n)); E = {idp: (0, 1, 2, 3)}; fr = [idp]
    while fr:
        nf = []
        for e in fr:
            for p, bp in G:
                f = tuple(p[e[x]] for x in range(n))
                if f not in E: E[f] = None; nf.append(f)
        fr = nf
    return list(E)
if __name__ == '__main__':
    tag = sys.argv[1]; a, c = int(tag[0]), int(tag[1])
    names, P, OS, G = gens(a, c); n = len(names)
    print('generators', len(G), 'group order', len(group(G, n)))
    U = np.load(f'st_{tag}.npz'); tr = U['tr'].tolist(); T = {t: i for i, t in enumerate(tr)}
    st = {}
    for b, o in zip(U['SB'].tolist(), U['SO'].tolist()): st.setdefault(b, set()).add(tuple(o))
    for p, bp in G:
        assert all(apply(p, t) in T for t in tr)
        for b in tr:
            img = {tuple(o[bp.index(q)] for q in range(4)) for o in st[b]}
            assert img == st[apply(p, b)]
    print('universe and state sets invariant under all generators')
    if 'check' in sys.argv:
        NT = len(tr); M = np.zeros((NT, NT), bool); lo = 0
        files = {int(f.split('/')[-1][2:-4].split('_')[0]): f for f in glob.glob(f'cf_{tag}/r_*_*.npy') if 'tmp' not in f}
        while lo < NT:
            R = np.unpackbits(np.load(files[lo]), axis=1)[:, :NT].astype(bool); M[lo:lo + len(R)] = R; lo += len(R)
        M |= M.T
        for p, bp in G:
            g = np.array([T[apply(p, t)] for t in tr])
            print('generator', bp, 'matrix invariant:', bool((M[np.ix_(g, g)] == M).all()))
