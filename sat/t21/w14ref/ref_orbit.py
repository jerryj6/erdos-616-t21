"""REFEREE: root step. B* = {w,g0,g1,g2}. Group H = all permutations of core points within the regions alpha, gamma, m3,
a3, a4 (order 2*6*6*2*2 = 288); each fixes every P_q setwise (asserted) hence extends (identity on O_q, U) to an
automorphism of the labelled base. Check: every avoider of B* in MY universe is either in the dead clause of
w14_certdead.cnf or in the H-orbit of one of the 5 case units."""
import json, itertools, numpy as np
from ref_states import Pm, NAMES
from pairref import read_binary
T = np.load('../w14/w14_conf.npz')['T'].tolist(); mine = set(json.load(open('ref_feas.json'))['traces'])
idx = {n: a for a, n in enumerate(NAMES)}
regs = [['al0','al1'], ['g0','g1','g2'], ['m0','m1','m2'], ['a3_0','a3_1'], ['a4_0','a4_1']]
H = []
for perms in itertools.product(*[list(itertools.permutations(r)) for r in regs]):
    p = list(range(16))
    for r, pr in zip(regs, perms):
        for x, y in zip(r, pr): p[idx[x]] = idx[y]
    H.append(p)
app = lambda p, b: sum(1 << p[a] for a in range(16) if b >> a & 1)
assert len(H) == 288 and all(app(p, Pm[q]) == Pm[q] for p in H for q in range(4))
Bs = sum(1 << idx[x] for x in ('w', 'g0', 'g1', 'g2'))
assert all(app(p, Bs) == Bs for p in H)
# sigma (swap P2,P3) moves w -> v, so it is not in Stab(B*): |Stab| within the order-576 group is 288
reps = []
for c in (15116, 14968, 15954, 16054, 17917):
    _, _, other = read_binary(f'../w14/w14_cert2_{c}.cnf')
    u = [x for x in other if len(x) == 1]; assert len(u) == 1 and u[0][0] == c + 1, (c, u)
    reps.append(T[c])
    assert T[c] & Bs == 0, 'rep does not avoid B*'
orb = {app(p, r) for r in reps for p in H}
_, _, other = read_binary('../w14/w14_certdead.cnf')
need = [B for B in (sum(1 << a for a in cc) for cc in itertools.combinations(range(16), 4)) if all(B & Pm[q] for q in range(4))]
deadc = [c for c in other if len(c) > 1 and not any(all((T[x-1] & B) == 0 for x in c) and len(c) == sum(1 for i, t in enumerate(T) if t & B == 0) for B in need)]
assert len(deadc) == 1, len(deadc)
dead = {T[x - 1] for x in deadc[0]}
assert all(t & Bs == 0 for t in dead)
av = {t for t in mine if t & Bs == 0}
print('avoiders of B* (my universe)', len(av), 'dead', len(dead & av), 'orbit of reps', len(orb), 'orbit avoiders in universe', len(orb & av))
print('uncovered avoiders:', len(av - dead - orb), ' orbit not in my universe:', len(orb - mine), ' dead&orbit overlap', len(dead & orb))
