"""SECOND, deliberately naive implementation (shares nothing with tr_core's rule code; only base() names/masks are reused
for the bit<->name map, and base() itself is re-asserted literally here). For a state / state pair (+ overlap vector) it
BUILDS concrete 21-sets on explicit points and runs a generic lemma checker over the whole family {E1,E2,G,H,F[,F']}:
 A (all pairs >= 5), F1 (all triples share a point), L (every subfamily w/o common point has union >= 61), and at EVERY
 5-pair (X,Y) of the family: D1 for every other member L with N ⊄ L; R3 for singles; SA + CLS for singles of different types.
usage: python3 tr_indep.py TAG NSAMPLE [seed]   (samples conflict pairs from pairs_TAG.npy and random non-conflict pairs,
and random traces in/out of the universe)"""
import sys, itertools, random, numpy as np
from tr_core import base
tag = sys.argv[1]; NS = int(sys.argv[2]); random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
a, c = int(tag[0]), int(tag[1])
fl = (2 if 'x' in tag else 0) | (4 if 'k' in tag else 0) | (8 if 'w' in tag else 0) | (1 if 'n' in tag else 0)
names, P, OS = base(a, c); n = len(names); P = [int(p) for p in P]; OS = [int(x) for x in OS]
CORE = [('c', i) for i in range(n)]
OP = [[('o', q, k) for k in range(OS[q])] for q in range(4)]
BASE = [frozenset([('c', i) for i in range(n) if P[q] >> i & 1] + OP[q]) for q in range(4)]
assert all(len(e) == 21 for e in BASE) and len(frozenset().union(*BASE)) == 61
def cls(x, y):
    if x < 1 or y < 1 or x + y < 5: return False
    if not fl & 8 and (x < 2 or y < 2): return False
    if not fl & 4 and x + y < 6: return False
    if not fl & 2 and {x, y} == {2, 4}: return False
    if fl & 1 and {x, y} == {3, 4}: return False
    return True
def family_ok(Fam, must):
    """generic lemma check; only instances involving at least one index in `must` are tested"""
    m = len(Fam); R = range(m)
    for i, j in itertools.combinations(R, 2):
        if (i in must or j in must) and len(Fam[i] & Fam[j]) < 5: return False
    for S in itertools.chain.from_iterable(itertools.combinations(R, k) for k in range(3, m + 1)):
        if not any(i in must for i in S): continue
        if not frozenset.intersection(*[Fam[i] for i in S]) and len(frozenset().union(*[Fam[i] for i in S])) < 61: return False
        if len(S) == 3 and not frozenset.intersection(*[Fam[i] for i in S]): return False
    for X, Y in itertools.permutations(R, 2):
        N = Fam[X] & Fam[Y]
        if len(N) != 5: continue
        others = [k for k in R if k not in (X, Y)]
        for L in others:
            if (L in must or X in must or Y in must) and not N <= Fam[L] and len(Fam[L] & (Fam[X] | Fam[Y])) > 9: return False
        sing = [k for k in others if len(Fam[k] & N) == 1]
        for Z in sing:
            if (Z in must or X in must or Y in must) and (len(Fam[Z] & Fam[X]) != 5 or len(Fam[Z] & Fam[Y]) != 5): return False
        for Z1, Z2 in itertools.combinations(sing, 2):
            if not any(k in must for k in (X, Y, Z1, Z2)): continue
            if Fam[Z1] & Fam[Z2] & N: continue
            I = Fam[Z1] & Fam[Z2]
            if not I <= Fam[X] | Fam[Y]: return False
            if not cls(len(I & Fam[X] - Fam[Y]), len(I & Fam[Y] - Fam[X])): return False
    return True
def mk(b, o, tagU='u1', share=None):
    s = {('c', i) for i in range(n) if b >> i & 1}
    for q in range(4): s |= set(OP[q][:o[q]])
    u = 21 - len(s); s |= {(tagU, k) for k in range(u)}
    return frozenset(s)
def mk2(b2, o2, o1, z, zu, u1):
    s = {('c', i) for i in range(n) if b2 >> i & 1}
    for q in range(4):
        rest = o2[q] - z[q]
        if rest < 0 or o1[q] + rest > OS[q]: return None
        s |= set(OP[q][:z[q]]) | set(OP[q][OS[q] - rest:])
    u2 = 21 - len(s)
    if zu > min(u1, u2): return None
    s |= {('u1', k) for k in range(zu)} | {('u2', k) for k in range(u2 - zu)}
    return frozenset(s)
def pair_compatible(st1, st2):
    for b1, o1 in st1:
        F = mk(b1, o1); u1 = 21 - sum(1 for x in F if x[0] != 'u1') if False else sum(1 for x in F if x[0] == 'u1')
        for b2, o2 in st2:
            u2 = 21 - bin(b2).count('1') - sum(o2)
            for z in itertools.product(*[range(0, min(o1[q], o2[q]) + 1) for q in range(4)]):
                for zu in range(0, min(u1, u2) + 1):
                    G = mk2(b2, o2, o1, z, zu, u1)
                    if G is None or G == F: continue
                    if family_ok(BASE + [F, G], {4, 5}): return True
    return False
U = np.load(f'st_{tag}.npz'); tr = U['tr'].tolist()
S = {}
for b, o in zip(U['SB'].tolist(), U['SO'].tolist()): S.setdefault(b, []).append(tuple(o))
# (1) per-edge: sampled states must pass; sampled (trace, o) outside the universe must fail
bad = 0
for b in random.sample(tr, min(NS, len(tr))):
    for o in S[b]:
        if not family_ok(BASE + [mk(b, o)], {4}): bad += 1
out = 0; outbad = 0
for _ in range(NS):
    b = random.randrange(1 << n); o = tuple(random.randrange(0, OS[q] + 1) for q in range(4))
    if bin(b).count('1') + sum(o) > 21 or o in S.get(b, []): continue
    out += 1
    if family_ok(BASE + [mk(b, o)], {4}): outbad += 1
boxbad = 0; boxn = 0
for b in (random.sample(tr, min(NS, len(tr))) if 'pairsonly' not in sys.argv else []):
    k = bin(b).count('1')
    for o in itertools.product(*[range(0, OS[q] + 1) for q in range(4)]):
        if k + sum(o) > 21 or o in S[b]: continue
        boxn += 1
        if family_ok(BASE + [mk(b, o)], {4}): boxbad += 1
print('per-edge: full o-box of sampled universe traces: rejected states', boxn, 'passing generic check', boxbad, flush=True)
print('per-edge: sampled universe states failing generic check', bad, '| sampled non-universe states', out, 'passing generic check', outbad, flush=True)
pf = [x[10:] for x in sys.argv if x.startswith('pairsfile=')]
pairs = np.load(pf[0] if pf else f'pairs_{tag}.npy'); conf = set(map(tuple, pairs[np.random.default_rng(1).choice(len(pairs), NS, replace=False)].tolist()))
dis = 0
for i, j in conf:
    if pair_compatible([(tr[i], o) for o in S[tr[i]]], [(tr[j], o) for o in S[tr[j]]]): dis += 1; print('DISAGREE conflict', i, j, flush=True)
print('conflict pairs re-checked', len(conf), 'generic finds compatible', dis, flush=True)
nc = 0; dis2 = 0
if 'noncompat' not in sys.argv:
    import glob
    rows = {int(f.split('/')[-1][2:-4].split('_')[0]): f for f in glob.glob(f'cf_{tag}/r_*_*.npy') if 'tmp' not in f}
    los = sorted(rows)
    def isconf(i, j):   # i < j ; read the packed row of i from its chunk
        lo = max(l for l in los if l <= i); R = np.load(rows[lo], mmap_mode='r')
        return bool((R[i - lo, j >> 3] >> (7 - (j & 7))) & 1)
    while nc < NS:
        i, j = sorted(random.sample(range(len(tr)), 2))
        if isconf(i, j): continue
        nc += 1
        if not pair_compatible([(tr[i], o) for o in S[tr[i]]], [(tr[j], o) for o in S[tr[j]]]): dis2 += 1; print('DISAGREE compatible', i, j, flush=True)
print('non-conflict pairs re-checked', nc, 'generic finds conflict', dis2, flush=True)
