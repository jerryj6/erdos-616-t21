"""Wave 14: DFS case tree with global elimination at every node, on the pairwise model Phi.
Node = (forced list F, excluded list X). live = gac-alive minus X minus every trace conflicting with some f in F.
Propagation (PROVED rule of w14_gac): t live, t meets B', no live avoider of B' compatible with t  =>  t dead.
Node CLOSED if some needed B' has no live avoider, or a forced trace dies. Otherwise branch on the needed B' (not covered
by F) with fewest live avoiders t_1..t_k: child i = (F+[t_i], X+[t_1..t_{i-1}]) (complete case split).
Root: the 5 Stab(B*)-orbit representatives of the alive avoiders of B* (WLOG argument in w14_sac.py: every solution is
mapped by some g in Stab(B*) to one containing a representative), no exclusions.
Resumable: results appended to w14_tree.jsonl keyed by node path."""
import sys, os, json, itertools, time, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T); Cp = z['C']
def crow(rows): return np.unpackbits(Cp[rows], axis=1)[:, :NT].astype(bool)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = np.array([B for B in Bs if not any((P[i] & B) == 0 for i in range(4))], dtype=np.int64)
NB = len(need)
AV = ((T[:, None] & need[None, :]) == 0)
al = set(json.load(open('w14_gac_elim.json'))['alive'])
alive = np.array([int(t) in al for t in T])
sup = np.load('w14_sac_sup.npy')
cases = json.load(open('w14_sac_cases.json'))
LOG = 'w14_tree.jsonl'
done = {}
if os.path.exists(LOG):
    for line in open(LOG):
        try: r = json.loads(line); done[r['path']] = r
        except Exception: pass
t0 = time.time()
def node(F, X):
    live = alive.copy(); live[X] = False
    if len(F):
        CF_ = crow(F)
        if CF_[:, F].any(): return ('CLOSED-forced-conflict', '', 0, None, 0)
        live &= ~CF_.any(0)
    if not live[F].all(): return ('CLOSED-forced-excluded', '', 0, None, 0)
    rows = np.nonzero(live)[0]
    sc = sup[rows].astype(np.int32)
    R = np.nonzero(alive & ~live)[0]
    rnd = 0
    while True:
        rnd += 1
        if len(R):
            for a in range(0, len(rows), 1500):
                rr = rows[a:a+1500]
                if not live[rr].any(): continue
                comp = (~crow(rr)[:, R]).astype(np.float32)
                sc[a:a+1500] -= np.rint(comp @ AV[R].astype(np.float32)).astype(np.int32)
        lr = live[rows]
        tot = AV[rows[lr]].sum(0)
        if (tot == 0).any(): return ('CLOSED-wipeout', nm(int(need[int(np.argmax(tot == 0))])), int(lr.sum()), None, rnd)
        z0 = lr[:, None] & (sc == 0) & ~AV[rows]
        dead = rows[z0.any(1)]
        if set(dead.tolist()) & set(F.tolist()): return ('CLOSED-forced-dies', '', int(lr.sum()), None, rnd)
        if len(dead) == 0: break
        live[dead] = False; R = dead
    covered = AV[F].any(0) if len(F) else np.zeros(NB, bool)
    tot = np.where(covered, 10**9, tot)
    k = int(np.argmin(tot))
    br = [int(i) for i in rows[lr] if AV[i, k]]
    br.sort(key=lambda i: -int(sc[np.searchsorted(rows, i)].sum()))  # heuristic order only
    return ('BRANCH', nm(int(need[k])), int(lr.sum()), br, rnd)
reps = sorted(map(int, cases))
stack = [(f'R{r}', [r], []) for r in reversed(reps)]
nodes = 0
while stack:
    path, F, X = stack.pop()
    if path in done: r = done[path]
    else:
        st, info, nlive, br, rnd = node(np.array(F, dtype=np.int64), np.array(X, dtype=np.int64))
        r = {'path': path, 'status': st, 'info': info, 'live': nlive, 'br': br, 'rnd': rnd, 'F': F, 'nX': len(X)}
        with open(LOG, 'a') as fh: fh.write(json.dumps(r) + '\n'); fh.flush(); os.fsync(fh.fileno())
        nodes += 1
        print(path, st, info, 'live', nlive, 'branch', None if br is None else len(br), 'depth', len(F), round(time.time() - t0), flush=True)
    if r['status'] == 'BRANCH':
        br = r['br']
        for i in range(len(br) - 1, -1, -1):
            stack.append((path + '.' + str(i), F + [br[i]], X + br[:i]))
print('TREE DONE new nodes', nodes, flush=True)
open('w14_tree.DONE', 'w').write('done\n')
