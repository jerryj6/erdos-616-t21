"""Wave 14: case split + global elimination (singleton cover-AC) on the pairwise model Phi.
Pick a needed 4-set B* with few alive avoiders. Every solution contains an alive avoider of B*; by invariance of Phi under the
group G (C is G-invariant, checked below on random elements) and of the gac-alive set, WLOG it contains the representative r of
its Stab(B*)-orbit. Case r: x_r = 1, so every trace conflicting with r is false; then run the elimination rule of w14_gac.py
(t meets B', no alive avoider of B' compatible with t => x_t = 0) to fixpoint. A case is CLOSED if some needed B' loses all alive
avoiders or r itself is eliminated. All cases closed => Phi UNSAT.
Checkpoint: w14_sac_sup.npy (global supports), w14_sac_cases.json (per-case results; resumable)."""
import sys, os, json, itertools, time, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
from w14_group import G, app
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T); Cp = z['C']
def crow(rows): return np.unpackbits(Cp[rows], axis=1)[:, :NT].astype(bool)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = np.array([B for B in Bs if not any((P[i] & B) == 0 for i in range(4))], dtype=np.int64)
NB = len(need)
AV = ((T[:, None] & need[None, :]) == 0)
al = set(json.load(open('w14_gac_elim.json'))['alive'])
alive = np.array([int(t) in al for t in T])
def appv(p, arr):
    y = np.zeros_like(arr)
    for a in range(n): y |= ((arr >> a) & 1) << p[a]
    return y
LUT = np.full(1 << n, -1, dtype=np.int64); LUT[T] = np.arange(NT)
TI = np.array([LUT[appv(p, T)] for p, pi in G])
# invariance check of C on random rows/group elements
rs = np.random.default_rng(1)
for g in rs.choice(len(G), 6, replace=False):
    rows = rs.choice(NT, 40, replace=False)
    A = crow(rows); Bm = crow(TI[g][rows])
    # exact statement: C[i,j] == C[g i, g j]
    assert (A == Bm[:, TI[g]]).all(), 'C not invariant'
print('C invariance spot-check OK', flush=True)
AL = np.nonzero(alive)[0]
SUPF = 'w14_sac_sup.npy'
t0 = time.time()
if os.path.exists(SUPF): sup = np.load(SUPF)
else:
    AVa = AV[AL].astype(np.float32)
    sup = np.zeros((NT, NB), np.int16)
    for a in range(0, len(AL), 800):
        rows = AL[a:a+800]
        comp = (~crow(rows)[:, AL]).astype(np.float32)
        comp[np.arange(len(rows)), a + np.arange(len(rows))] = 0
        sup[rows] = np.rint(comp @ AVa).astype(np.int16)
        print('sup rows', a, round(time.time() - t0), flush=True)
    np.save(SUPF, sup)
# check global fixpoint consistency
zero = (sup[AL] == 0) & ~AV[AL]
print('global zero-support entries among alive (should be 0):', int(zero.sum()), flush=True)
cnt = AV[AL].sum(0)
order = np.argsort(cnt)
Bstar = int(need[order[0]]); kB = int(order[0])
stab = [g for g, (p, pi) in enumerate(G) if app(p, Bstar) == Bstar]
cands = [i for i in AL if AV[i, kB]]
reps = []; seen = set()
for i in cands:
    if i in seen: continue
    reps.append(int(i)); seen |= {int(TI[g][i]) for g in stab}
print('B*', nm(Bstar), 'alive avoiders', len(cands), '|Stab|', len(stab), 'cases', len(reps), flush=True)
CF = 'w14_sac_cases.json'
res = json.load(open(CF)) if os.path.exists(CF) else {}
for r in reps:
    if str(r) in res: continue
    rowr = crow([r])[0]
    ac = alive & ~rowr; ac[r] = True
    R = np.nonzero(alive & rowr)[0]
    rows = np.nonzero(ac)[0]
    sc = sup[rows].astype(np.int32)
    out = None; rnd = 0; elim = 0
    while True:
        rnd += 1
        if len(R):
            for a in range(0, len(rows), 1500):
                rr = rows[a:a+1500]
                comp = (~crow(rr)[:, R]).astype(np.float32)
                sc[a:a+1500] -= np.rint(comp @ AV[R].astype(np.float32)).astype(np.int32)
        live = ac[rows]
        tot = AV[rows[live]].sum(0)
        if (tot == 0).any():
            out = ('CLOSED-wipeout', nm(int(need[int(np.nonzero(tot == 0)[0][0])]))); break
        z0 = live[:, None] & (sc == 0) & ~AV[rows]
        dead = rows[z0.any(1)]
        if r in set(dead.tolist()):
            out = ('CLOSED-r-eliminated', nm(int(need[int(np.nonzero(z0[np.searchsorted(rows, r)])[0][0])]))); break
        if len(dead) == 0:
            out = ('OPEN-fixpoint', int(live.sum())); break
        ac[dead] = False; R = dead; elim += len(dead)
    res[str(r)] = [nm(int(T[r])), out[0], out[1], rnd, elim]
    json.dump(res, open(CF + '.tmp', 'w')); os.replace(CF + '.tmp', CF)
    print('case', nm(int(T[r])), out, 'rounds', rnd, 'elim', elim, round(time.time() - t0), flush=True)
closed = sum(1 for v in res.values() if v[1].startswith('CLOSED'))
print('cases', len(reps), 'closed', closed, flush=True)
if closed == len(reps): open('w14_sac.UNSAT', 'w').write('all cases closed\n')
open('w14_sac.DONE', 'w').write(f'{closed}/{len(reps)}\n')
