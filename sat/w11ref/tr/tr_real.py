"""positive control: literal configurations (authors' violation-free 16-single realizations, DATA only) must pass
every per-edge rule and every pair rule AT THEIR TRUE OVERLAPS, and their traces must be in the universe.
Also checks first the literal facts the rules presuppose (21-uniform, base labelling exact).
usage: python3 tr_real.py a c REAL.json [n34]"""
import sys, json, itertools, numpy as np
from tr_core import base, edge_ok, pair_rules, pc
a, c = int(sys.argv[1]), int(sys.argv[2]); d = json.load(open(sys.argv[3])); n34 = (1 if 'n34' in sys.argv else 0) | (2 if 'no24' in sys.argv else 0) | (4 if 'nonk' in sys.argv else 0) | (8 if 'now7' in sys.argv else 0)
names, P, OS = base(a, c); n = len(names); FULL = (1 << n) - 1
E = [frozenset(e) for e in d['edges']]; assert all(len(e) == 21 for e in E)
B = E[:4]; idx = {nm: i for i, nm in enumerate(names)}
core = set(names)
for q in range(4):  # base labelling: core part of B_q equals P_q, private part has OS_q points, disjoint from other base edges
    assert {x for x in B[q] if x in core} == {names[i] for i in range(n) if P[q] >> i & 1}, q
    priv = B[q] - core; assert len(priv) == OS[q] and all(not (priv & B[r]) for r in range(4) if r != q)
O = [B[q] - core for q in range(4)]; allbase = set().union(*B)
st = []
for e in E[4:]:
    b = sum(1 << idx[x] for x in e if x in core); o = np.array([len(e & O[q]) for q in range(4)], np.int64)
    st.append((b, o, e))
nbad = sum(1 for b, o, e in st if not edge_ok(b, o, P, OS, FULL, n34))
U = np.load(f'st_{a}{c}' + ('n' if n34 & 1 else '') + ('x' if n34 & 2 else '') + ('k' if n34 & 4 else '') + ('w' if n34 & 8 else '') + '.npz'); T = set(U['tr'].tolist())
print('non-base edges', len(st), 'edge_ok failures', nbad, 'traces not in universe', sum(1 for b, o, e in st if b not in T))
bad = 0; npair = 0
for (b1, o1, e1), (b2, o2, e2) in itertools.combinations(st, 2):
    if e1 == e2: continue
    npair += 1
    z = np.array([len(e1 & e2 & O[q]) for q in range(4)], np.int64); zu = len((e1 & e2) - allbase)
    x1 = np.array([pc(b1 & P[q]) + o1[q] for q in range(4)], np.int64); x2 = np.array([pc(b2 & P[q]) + o2[q] for q in range(4)], np.int64)
    u1 = 21 - pc(b1) - o1.sum(); u2 = 21 - pc(b2) - o2.sum()
    if not pair_rules(b1, o1, x1, u1, b2, o2, x2, u2, b1 & b2, z, zu, P, OS, FULL, n34, 0): bad += 1
print('pairs', npair, 'pair_rules violations at true overlaps', bad)
