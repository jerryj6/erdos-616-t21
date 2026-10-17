"""Wave 14 global model, lazy over constraints (NOT over edges): variables x_t for all 18217 feasible core traces
(t = core part of some non-base edge); cover clause for every core 4-set B not avoided by a base edge:
OR_{t & B = 0} x_t  (tau >= 5 restricted to core 4-sets).  Conflict clauses (-x_t v -x_t') are added lazily from the
precomputed sound conflict matrix (w14_conf.npz), with all 576 group images, whenever a minimal sub-cover of the
current model contains a conflicting pair. Stops at UNSAT or at a pairwise-conflict-free minimal cover (pairwise STALL).
Checkpoint: w14_lazy_pairs.npy (list of added (i,j) index pairs)."""
import sys, os, json, itertools, time, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
from w14_group import G
from pysat.solvers import Solver
DROP = os.environ.get('W14DROP', '')
SUF = ('_drop' + DROP.replace(',', '_')) if DROP else ''
z = np.load(f'w14_conf{SUF}.npz'); T = z['T']; NT = len(T)
Cp = z['C']  # packed conflict rows; unpacked on demand (memory)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = [B for B in Bs if not any((P[i] & B) == 0 for i in range(4))]
def appv(p, arr):
    y = np.zeros_like(arr)
    for a in range(n): y |= ((arr >> a) & 1) << p[a]
    return y
LUT = np.full(1 << n, -1, dtype=np.int64); LUT[T] = np.arange(NT)
TI = np.array([LUT[appv(p, T)] for p, pi in G])  # TI[g][i]
cover = [[int(i) + 1 for i in np.nonzero((T & B) == 0)[0]] for B in need]
PF = f'w14_lazy_pairs{SUF}.npy'
open(f'run_lazy{SUF}.pypid','w').write(str(os.getpid()))
ADD = np.zeros((NT, NT), bool)
if os.path.exists(PF):
    pp = np.load(PF); ADD[pp[:, 0], pp[:, 1]] = True; del pp
npairs = int(ADD.sum())
s = Solver(name='cadical153', bootstrap_with=cover)
if not SUF and os.path.exists('w14_gac_elim.json'):   # units from the sound global elimination (w14_gac.py)
    GA = json.load(open('w14_gac_elim.json'))
    if 'alive' in GA:
        al = set(GA['alive'])
        for i in range(NT):
            if int(T[i]) not in al: s.add_clause([-(i + 1)])
        print('gac units', NT - len(al), flush=True)
for i, j in np.argwhere(ADD): s.add_clause([-(int(i) + 1), -(int(j) + 1)])
print('vars', NT, 'cover clauses', len(cover), 'loaded pairs', npairs, flush=True)
def save():
    np.save(PF + '.tmp.npy', np.argwhere(ADD).astype(np.int32)); os.replace(PF + '.tmp.npy', PF)
t0 = time.time(); it = 0
while True:
    it += 1
    r = s.solve()
    if not r:
        print('UNSAT at it', it, 'pairs', npairs, round(time.time() - t0, 1), flush=True)
        save(); open(f'w14_lazy{SUF}.UNSAT', 'w').write(str(npairs)); break
    m = set(l for l in s.get_model() if l > 0); on = [i for i in range(NT) if i + 1 in m]
    # minimal sub-cover: greedy keep order by size (small traces first), then prune redundant
    on.sort(key=lambda i: bin(int(T[i])).count('1'))
    needA = np.array(need, dtype=np.int64)
    covered = np.zeros(len(need), bool); S0 = []
    for i in on:
        c = (needA & T[i]) == 0
        if (c & ~covered).any(): S0.append(i); covered |= c
    assert covered.all()
    sub = np.array(S0)
    CC = np.unpackbits(Cp[sub], axis=1)[:, :NT][:, sub].astype(bool)
    bad = np.argwhere(np.triu(CC, 1))
    if len(bad) == 0:
        print('PAIRWISE STALL at it', it, 'cover size', len(S0), flush=True)
        json.dump([int(T[i]) for i in S0], open(f'w14_lazy_stall{SUF}.json', 'w')); break
    I0 = sub[bad[:, 0]]; J0 = sub[bad[:, 1]]
    X = TI[:, I0].ravel(); Y = TI[:, J0].ravel()
    a = np.minimum(X, Y); b = np.maximum(X, Y)
    fresh = ~ADD[a, b]
    a = a[fresh]; b = b[fresh]
    key = np.unique(a.astype(np.int64) * NT + b)
    a = key // NT; b = key % NT
    ADD[a, b] = True; npairs += len(a)
    for i, j in zip(a.tolist(), b.tolist()): s.add_clause([-(i + 1), -(j + 1)])
    if it % 5 == 0: save()
    print(f'it {it} on {len(on)} cover {len(S0)} conflicts {len(bad)} new {len(a)} total {npairs} t {time.time()-t0:.0f}', flush=True)
