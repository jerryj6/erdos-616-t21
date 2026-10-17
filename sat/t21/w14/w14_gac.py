"""Wave 14 global elimination ("cover-AC") on the pairwise trace model.
Rule (PROVED sound): if trace t meets B' (t&B' != 0) and every ALIVE trace avoiding B' conflicts with t, then x_t is false
in every solution (cover clause of B' + binary conflicts give -x_t by unit propagation = a RUP lemma). Iterate.
If some needed B loses all alive avoiders, the model is UNSAT; the eliminations in order form a DRAT proof (unit lemmas).
Uses group equivariance (C, cover family and alive set are invariant), computing supports for orbit representatives of B' only.
Output: w14_gac_elim.json = list of rounds, each a list of [trace, B'] eliminations (one witness B' per trace)."""
import sys, json, itertools, time, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
from w14_group import G, app
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T)
C = np.unpackbits(z['C'], axis=1)[:, :NT].astype(bool)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = [B for B in Bs if not any((P[i] & B) == 0 for i in range(4))]
reps = []; seen = set()
for B in need:
    if B in seen: continue
    reps.append(B); seen |= {app(p, B) for p, pi in G}
def appv(p, arr):
    y = np.zeros_like(arr)
    for a in range(n): y |= ((arr >> a) & 1) << p[a]
    return y
LUT = np.full(1 << n, -1, dtype=np.int64); LUT[T] = np.arange(NT)
TI = np.array([LUT[appv(p, T)] for p, pi in G])
AV = np.array([(T & B) == 0 for B in reps]).T  # NT x R  (t avoids rep B)
print('needed B', len(need), 'orbit reps', len(reps), flush=True)
alive = np.ones(NT, bool)
rounds = []; t0 = time.time()
CH = 1500
while True:
    V = (AV & alive[:, None]).astype(np.float32)          # alive avoiders of each rep
    tot = V.sum(0)
    if (tot == 0).any():
        k = int(np.nonzero(tot == 0)[0][0])
        print('WIPEOUT: B', nm(reps[k]), 'has no alive avoider -> UNSAT', flush=True)
        json.dump({'rounds': rounds, 'wipeout': reps[k]}, open('w14_gac_elim.json', 'w')); break
    sup = np.empty((NT, len(reps)), np.float32)
    for a in range(0, NT, CH):
        sup[a:a+CH] = tot[None, :] - C[a:a+CH].astype(np.float32) @ V
    zero = (sup < 0.5) & ~AV & alive[:, None]   # t meets B' and no compatible alive avoider
    E = np.nonzero(zero.any(1))[0]
    if len(E) == 0:
        print('FIXPOINT alive', int(alive.sum()), round(time.time() - t0), flush=True)
        json.dump({'rounds': rounds, 'alive': [int(x) for x in T[alive]]}, open('w14_gac_elim.json', 'w')); break
    rec = []
    newdead = np.zeros(NT, bool)
    for i in E:
        k = int(np.nonzero(zero[i])[0][0])
        for g, (p, pi) in enumerate(G):
            j = TI[g][i]
            if not newdead[j]: newdead[j] = True; rec.append([int(T[j]), app(p, reps[k])])
    alive &= ~newdead
    rounds.append(rec)
    print('round', len(rounds), 'eliminated', int(newdead.sum()), 'alive', int(alive.sum()), round(time.time() - t0), flush=True)
