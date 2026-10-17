"""Wave 14: DRAT certificate for one root case r of the w14_tree search (pairwise model Phi with unit x_r).
Replays the tree of w14_tree.jsonl under root R<r> (same branching lists), logging for every elimination a witness B'
(the zero-support needed 4-set with fewest live avoiders) and emitting RUP lemmas:
  global gac (w14_gac_elim.json, rounds 1..k):           [-t]
  node with cube A (F positive, X negative), elimination: [-A..., -t]
  node closed / all children closed:                     [-A...]
  root (A = [x_r]) closed:                                [-x_r], then the empty clause (x_r is a unit of the CNF).
CNF_r = all 1730 COV clauses (FULL avoider lists over the 18217 traces) + the CONF binary clauses used by some RUP step
+ unit [x_r]. Variables: trace index + 1.  Usage: python3 w14_cert.py r"""
import sys, os, json, itertools, time, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
r0 = int(sys.argv[1])
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T); Cp = z['C']
def crow(rows): return np.unpackbits(Cp[rows], axis=1)[:, :NT].astype(bool)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = np.array([B for B in Bs if not any((P[i] & B) == 0 for i in range(4))], dtype=np.int64)
NB = len(need)
AV = ((T[:, None] & need[None, :]) == 0)
LUT = {int(t): i for i, t in enumerate(T)}
GA = json.load(open('w14_gac_elim.json'))
al = set(GA['alive']); alive = np.array([int(t) in al for t in T])
sup = np.load('w14_sac_sup.npy')
tree = {}
for line in open('w14_tree.jsonl'):
    rr = json.loads(line); tree[rr['path']] = rr
conf = []      # list of int64 arrays of keys i*NT+j (i<j)
def addconf(i, js):
    js = np.asarray(js, dtype=np.int64)
    if len(js) == 0: return
    a = np.minimum(i, js); b = np.maximum(i, js); conf.append(a * NT + b)
out = open(f'w14_cert_{r0}.drat.tmp', 'w')
nlem = 0
def lemma(lits):
    global nlem
    out.write(' '.join(map(str, lits)) + ' 0\n'); nlem += 1
# --- global gac lemmas
gal = np.ones(NT, bool)
for rnd in GA['rounds']:
    dead = [LUT[t] for t, B in rnd]
    for t, B in rnd:
        i = LUT[t]; k = int(np.nonzero(need == B)[0][0])
        avs = np.nonzero(AV[:, k] & gal)[0]
        Ci = crow([i])[0]
        assert Ci[avs].all() and not AV[i, k], 'gac witness invalid'
        addconf(i, avs); lemma([-(i + 1)])
    gal[dead] = False
assert (gal == alive).all()
t0 = time.time()
def node(path, F, X):
    """emit lemmas for node; returns status record (must match tree)"""
    A = [-(f + 1) for f in F] + [x + 1 for x in X]   # clause prefix = negated cube
    live = alive.copy(); live[X] = False
    if len(F):
        CF_ = crow(F)
        if CF_[:, F].any():
            a, b = np.argwhere(CF_[:, F])[0]; addconf(F[a], [F[b]]); return 'CLOSED-forced-conflict'
        for q, f in enumerate(F):
            js = np.nonzero(CF_[q] & alive & live)[0]
            addconf(f, js); live[js] = False
    if not live[F].all(): return 'CLOSED-forced-excluded'
    rows = np.nonzero(live)[0]
    sc = sup[rows].astype(np.int32)
    R = np.nonzero(alive & ~live)[0]
    while True:
        if len(R):
            for a in range(0, len(rows), 1500):
                rr = rows[a:a+1500]
                if not live[rr].any(): continue
                comp = (~crow(rr)[:, R]).astype(np.float32)
                sc[a:a+1500] -= np.rint(comp @ AV[R].astype(np.float32)).astype(np.int32)
        lr = live[rows]
        tot = AV[rows[lr]].sum(0)
        if (tot == 0).any(): return 'CLOSED-wipeout'
        z0 = lr[:, None] & (sc == 0) & ~AV[rows]
        di = np.nonzero(z0.any(1))[0]
        if len(di) == 0: break
        forced_dies = False
        for d in di:
            t = int(rows[d]); cand = np.nonzero(z0[d])[0]
            k = int(cand[np.argmin(tot[cand])])
            avs = rows[lr & AV[rows, k]]
            Ct = crow([t])[0]; assert Ct[avs].all()
            addconf(t, avs); lemma(A + [-(t + 1)])
            if t in F: forced_dies = True
        if forced_dies: return 'CLOSED-forced-dies'
        dead = rows[di]; live[dead] = False; R = dead
    return 'BRANCH'
def solve(path, F, X):
    rec = tree[path]
    st = node(path, F, X)
    assert st == rec['status'], (path, st, rec['status'])
    if st == 'BRANCH':
        br = rec['br']
        for i in range(len(br)):
            solve(path + '.' + str(i), F + [br[i]], X + br[:i])
    if len(F) + len(X) > 1 or path != f'R{r0}':
        lemma([-(f + 1) for f in F] + [x + 1 for x in X])
sys.setrecursionlimit(10000)
solve(f'R{r0}', [r0], [])
lemma([-(r0 + 1)]); lemma([])
out.close(); os.replace(f'w14_cert_{r0}.drat.tmp', f'w14_cert_{r0}.drat')
keys = np.unique(np.concatenate(conf)) if conf else np.zeros(0, np.int64)
cov = [[int(i) + 1 for i in np.nonzero(AV[:, k])[0]] for k in range(NB)]
with open(f'w14_cert_{r0}.cnf.tmp', 'w') as fh:
    fh.write(f'p cnf {NT} {len(cov) + len(keys) + 1}\n')
    for c in cov: fh.write(' '.join(map(str, c)) + ' 0\n')
    for kk in keys.tolist(): fh.write(f'-{kk // NT + 1} -{kk % NT + 1} 0\n')
    fh.write(f'{r0 + 1} 0\n')
os.replace(f'w14_cert_{r0}.cnf.tmp', f'w14_cert_{r0}.cnf')
np.save(f'w14_cert_{r0}_conf.npy', keys)
print('case', r0, nm(int(T[r0])), 'lemmas', nlem, 'conf clauses', len(keys), 'time', round(time.time() - t0), flush=True)
