"""Root step of the Wave 14 certificate.
B* = the needed 4-set chosen in w14_sac.py. Every solution of Phi has an avoider t of B* (COV(B*)). Either t is gac-dead,
refuted here: CNF_dead = COV + CONF clauses of the gac lemmas + clause (OR of the gac-dead avoiders of B*), DRAT = the gac
lemmas then the empty clause; or t is alive, and then t = g(r) for g in Stab(B*) and one of the 5 representatives r
(checked here: the Stab(B*)-orbits of the 5 reps cover exactly the alive avoiders), refuted by w14_cert2_<r> + symmetry."""
import sys, json, itertools, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
from w14_group import G, app
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = np.array([B for B in Bs if not any((P[i] & B) == 0 for i in range(4))], dtype=np.int64)
AV = ((T[:, None] & need[None, :]) == 0)
LUT = {int(t): i for i, t in enumerate(T)}
GA = json.load(open('w14_gac_elim.json')); al = set(GA['alive'])
reps = sorted(map(int, json.load(open('w14_sac_cases.json'))))
# B*: must be the set all reps avoid with min alive avoiders; recompute as in w14_sac
alive = np.array([int(t) in al for t in T])
cnt = AV[alive].sum(0); kB = int(np.argsort(cnt)[0]); Bstar = int(need[kB])
assert all(AV[r, kB] for r in reps)
stab = [(p, pi) for p, pi in G if app(p, Bstar) == Bstar]
orb = set()
for r in reps:
    for p, pi in stab: orb.add(LUT[app(p, int(T[r]))])
alive_av = set(int(i) for i in np.nonzero(alive & AV[:, kB])[0])
print('B*', nm(Bstar), '|Stab|', len(stab), 'alive avoiders', len(alive_av), 'covered by rep orbits', orb == alive_av, flush=True)
assert orb == alive_av
dead_av = [int(i) for i in np.nonzero(~alive & AV[:, kB])[0]]
print('gac-dead avoiders of B*', len(dead_av))
gal = np.ones(NT, bool); gconf = []; GL = []
for rnd in GA['rounds']:
    dead = [LUT[t] for t, B in rnd]
    for t, B in rnd:
        i = LUT[t]; k = int(np.nonzero(need == B)[0][0])
        avs = np.nonzero(AV[:, k] & gal)[0]
        gconf.append(np.minimum(i, avs) * NT + np.maximum(i, avs)); GL.append(i)
    gal[dead] = False
keys = np.unique(np.concatenate(gconf))
with open('w14_certdead.cnf', 'w') as fh:
    fh.write(f'p cnf {NT} {len(need) + len(keys) + 1}\n')
    for k in range(len(need)): fh.write(' '.join(str(int(i) + 1) for i in np.nonzero(AV[:, k])[0]) + ' 0\n')
    for kk in keys.tolist(): fh.write(f'-{kk // NT + 1} -{kk % NT + 1} 0\n')
    fh.write(' '.join(str(i + 1) for i in dead_av) + ' 0\n')
with open('w14_certdead.drat', 'w') as fh:
    for i in GL: fh.write(f'-{i + 1} 0\n')
    fh.write('0\n')
np.save('w14_certdead_conf.npy', keys)
print('conf clauses', len(keys), 'lemmas', len(GL) + 1)
