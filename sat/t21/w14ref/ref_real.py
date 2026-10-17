"""REFEREE: the 12 literal K4 realizations. For each file: (1) literal check: 21-uniform, base = (3,2,1,1)-K4 in the
labelling (core names -> my regions), property L on EVERY subfamily (union <= 60 => common point); (2) every non-base
edge's (trace, o) is a state of MY enumeration; (3) every pair of non-base edges with distinct traces is compatible under
MY pairwise rules (pairref.feasible over my states of those traces) AND the exact-state pair itself is compatible;
(4) the realization's distinct core traces satisfy every binary clause of the case CNFs (no clause kills a realization)."""
import json, itertools, numpy as np
from ref_states import Pm, NAMES, ok as state_ok, pc
from pairref import feasible, P, OS, read_binary
W8 = ['T012_0','T013_0','T023_0','T023_1','T123_0','T123_1','T123_2','p01_0','p01_1','p01_2','p02_0','p02_1','p03_0','p03_1','p12_0','p13_0']
w8 = {s: a for a, s in enumerate(W8)}
files = ['w12_M10_real_keep.json','w11_B_real_keep.json','w10x_w12b1_real.json','w10x_w12Br1_real.json','w10x_w12Br2_real.json',
         'w10x_w12Pr0_real.json','w10x_w12Pr1_real.json','w10x_w12Pr2_real.json','w10x_w12Tr0_real.json','w10x_w12Tr1_real.json',
         'w10x_w12Ur0_real.json','w10x_w12m1_real.json']
T = np.load('../w14/w14_conf.npz')['T'].tolist(); lut = {t: i + 1 for i, t in enumerate(T)}
conf = set()
for c in (15116, 14968, 15954, 16054, 17917):
    pa, pb, _ = read_binary(f'../w14/w14_cert2_{c}.cnf'); conf |= set(zip(pa.tolist(), pb.tolist()))
pa, pb, _ = read_binary('../w14/w14_certdead.cnf'); conf |= set(zip(pa.tolist(), pb.tolist()))
tot = dict(edges=0, pairs=0, Lviol=0, statebad=0, pairbad=0, cnfbad=0)
for f in files:
    d = json.load(open('../' + f)); names = d.get('names') or d.get('named')
    E = []; lab = d['labels']
    for e in d['edges']:
        S = frozenset((names[x] if x < len(names) else f'U{x}') if isinstance(x, int) else x for x in e)
        E.append(S)
    assert all(len(e) == 21 for e in E), f
    bi = [lab.index(x) for x in (['B0','B1','B2','B3'] if 'B0' in lab else ['P0','P1','P2','P3'])]
    base = [E[i] for i in bi]
    # base must realise the labelling: core point named p lies exactly in the base edges of its region
    for s, a in w8.items():
        assert {q for q in range(4) if s in base[q]} == {q for q in range(4) if Pm[q] >> a & 1}, (f, s)
    core = set(W8)
    for q in range(4):
        priv = base[q] - core
        assert all(not (priv & base[r]) for r in range(4) if r != q) and len(priv) == OS[q], f
    # property L literally on every subfamily
    m = len(E); lv = 0
    for mask in range(1, 1 << m):
        fam = [E[i] for i in range(m) if mask >> i & 1]
        U = frozenset().union(*fam)
        if len(U) <= 60 and not frozenset.intersection(*fam): lv += 1
    tot['Lviol'] += lv
    St = []
    for i, e in enumerate(E):
        if i in bi: continue
        b = sum(1 << w8[s] for s in e if s in w8)
        o = tuple(len(e & (base[q] - core)) for q in range(4))
        tot['edges'] += 1
        if not state_ok(b, o): tot['statebad'] += 1; print('STATE REJECTED', f, lab[i])
        St.append((lab[i], b, np.array(o, np.int64)))
    for x, y in itertools.combinations(range(len(St)), 2):
        tot['pairs'] += 1
        (l1, b1, o1), (l2, b2, o2) = St[x], St[y]
        if not feasible(b1, o1, b2, o2, P, OS): tot['pairbad'] += 1; print('PAIR REJECTED', f, l1, l2)
        if b1 != b2:
            v1, v2 = lut.get(b1), lut.get(b2)
            if v1 and v2 and ((v1, v2) in conf or (v2, v1) in conf): tot['cnfbad'] += 1; print('CNF CLAUSE KILLS', f, l1, l2)
    print(f, 'edges', len(E), 'L-violations', lv, flush=True)
print(tot)
