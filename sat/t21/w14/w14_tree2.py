"""Wave 14: DFS case tree with incremental global elimination AND on-the-fly DRAT emission, one root case r per run.
Same rule and same branching rule as w14_tree.py (branch on the uncovered needed B with fewest live avoiders; child i forces
t_i, excludes t_1..t_{i-1}); supports are updated incrementally from the parent (faster). Lemmas (RUP):
  elimination of t at a node with cube A:  (negA v -x_t), witness B' = zero-support needed set with fewest live avoiders;
  node closed or all children closed:      (negA).
CONF clauses used are collected: (t, live avoiders of B') for each elimination, (t_i, traces killed by forcing t_i).
Resumable per root child: w14_t2_<r>/child<i>.drat + child<i>_conf.npy + child<i>.done; root part in root.drat/root_conf.npy.
Final assembly (when all children done): w14_cert2_<r>.cnf / .drat (global gac lemmas + root + children + [-x_r] + []).
Usage: python3 w14_tree2.py r"""
import sys, os, json, itertools, time, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm
r0 = int(sys.argv[1])
D = f'w14_t2_{r0}'; os.makedirs(D, exist_ok=True)
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T); Cp = z['C']
def crow(rows): return np.unpackbits(Cp[rows], axis=1)[:, :NT].astype(bool)
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = np.array([B for B in Bs if not any((P[i] & B) == 0 for i in range(4))], dtype=np.int64)
NB = len(need)
AV = ((T[:, None] & need[None, :]) == 0)
AVf = AV.astype(np.float32)
LUT = {int(t): i for i, t in enumerate(T)}
GA = json.load(open('w14_gac_elim.json'))
al = set(GA['alive']); alive = np.array([int(t) in al for t in T])
sup = np.load('w14_sac_sup.npy')
t0 = time.time(); stats = {'nodes': 0, 'lemmas': 0}
class Out:
    def __init__(s, path): s.fh = open(path + '.tmp', 'w'); s.path = path; s.conf = []
    def lemma(s, lits): s.fh.write(' '.join(map(str, lits)) + ' 0\n'); stats['lemmas'] += 1
    def addconf(s, i, js):
        js = np.asarray(js, dtype=np.int64)
        if len(js):
            s.conf.append(np.minimum(i, js) * NT + np.maximum(i, js)); s.nc = getattr(s, 'nc', 0) + len(js)
            if s.nc > 4_000_000:
                s.conf = [np.unique(np.concatenate(s.conf))]; s.nc = len(s.conf[0])
    def close(s):
        s.fh.close(); os.replace(s.path + '.tmp', s.path)
        k = np.unique(np.concatenate(s.conf)) if s.conf else np.zeros(0, np.int64)
        np.save(s.path + '_conf.npy', k)
def update(sc, rows, live, Dd):
    """sc -= (#compatible avoiders among Dd) for live rows"""
    if len(Dd) == 0: return
    li = np.nonzero(live[rows])[0]
    for a in range(0, len(li), 2000):
        ii = li[a:a+2000]
        comp = (~crow(rows[ii])[:, Dd]).astype(np.float32)
        sc[ii] -= np.rint(comp @ AVf[Dd]).astype(sc.dtype)
def propagate(out, F, X, live, rows, sc):
    """eliminate to fixpoint, emitting lemmas. returns ('CLOSED',info) or ('BRANCH', k, branchlist)"""
    A = [-(f + 1) for f in F] + [x + 1 for x in X]
    Fs = set(F)
    while True:
        lr = live[rows]
        tot = AV[rows[lr]].sum(0)
        if (tot == 0).any(): return ('CLOSED', 'wipeout ' + nm(int(need[int(np.argmax(tot == 0))])))
        z0 = lr[:, None] & (sc == 0) & ~AV[rows]
        di = np.nonzero(z0.any(1))[0]
        if len(di) == 0: break
        dies = False
        for d in di:
            t = int(rows[d]); cand = np.nonzero(z0[d])[0]
            k = int(cand[np.argmin(tot[cand])])
            avs = rows[lr & AV[rows, k]]
            out.addconf(t, avs); out.lemma(A + [-(t + 1)])
            if t in Fs: dies = True
        if dies: return ('CLOSED', 'forced dies')
        dead = rows[di]; live[dead] = False
        update(sc, rows, live, dead)
    covered = AV[F].any(0)
    tot2 = np.where(covered, 10**9, tot)
    k = int(np.argmin(tot2))
    br = [int(i) for i in rows[lr] if AV[i, k]]
    return ('BRANCH', k, br)
def child_state(live, rows, sc, F, X, br, i, out):
    t = br[i]
    nl = live.copy()
    Ct = crow([t])[0]
    if any(Ct[f] for f in F): return None  # cannot happen: t live means compatible with F
    killed = np.nonzero(nl & Ct)[0]
    out.addconf(t, killed)
    nl[killed] = False; nl[br[:i]] = False
    Dd = np.nonzero(live & ~nl)[0]
    sc2 = sc.copy(); update(sc2, rows, nl, Dd)
    return nl, sc2
def dfs(out, F, X, live, rows, sc, depth):
    stats['nodes'] += 1
    res = propagate(out, F, X, live, rows, sc)
    if res[0] == 'BRANCH':
        _, k, br = res
        for i in range(len(br)):
            st = child_state(live, rows, sc, F, X, br, i, out)
            dfs(out, F + [br[i]], X + br[:i], st[0], rows, st[1], depth + 1)
    out.lemma([-(f + 1) for f in F] + [x + 1 for x in X])
    if depth <= 2: print('  closed', depth, len(F), len(X), stats, round(time.time() - t0), flush=True)
# ---- root of case r0
Ct = crow([r0])[0]
live = alive & ~Ct
rows = np.nonzero(live)[0]
sc = sup[rows].astype(np.int16)
Dd = np.nonzero(alive & ~live)[0]
update(sc, rows, live, Dd)
rootf = f'{D}/root.drat'
root = Out(rootf)
root.addconf(r0, Dd)
res = propagate(root, [r0], [], live, rows, sc)
print('case', r0, nm(int(T[r0])), 'root', res[0], res[1] if res[0] == 'CLOSED' else (nm(int(need[res[1]])), len(res[2])), flush=True)
br = res[2] if res[0] == 'BRANCH' else []
for i in range(len(br)):
    cf = f'{D}/child{i}.drat'
    if os.path.exists(cf + '.done'): continue
    o = Out(cf)
    st = child_state(live, rows, sc, [r0], [], br, i, o)
    dfs(o, [r0, br[i]], br[:i], st[0], rows, st[1], 1)
    o.close(); open(cf + '.done', 'w').write('ok\n')
    print('root child', i, 'of', len(br), 'done', stats, round(time.time() - t0), flush=True)
root.lemma([-(r0 + 1)]); root.lemma([])
root.close()
# ---- assemble
confs = [np.load(rootf + '_conf.npy')] + [np.load(f'{D}/child{i}.drat_conf.npy') for i in range(len(br))]
GL = []  # global gac lemmas + their conf clauses
gal = np.ones(NT, bool); gconf = []
for rnd in GA['rounds']:
    dead = [LUT[t] for t, B in rnd]
    for t, B in rnd:
        i = LUT[t]; k = int(np.nonzero(need == B)[0][0])
        avs = np.nonzero(AV[:, k] & gal)[0]
        gconf.append(np.minimum(i, avs) * NT + np.maximum(i, avs)); GL.append(i)
    gal[dead] = False
keys = np.unique(np.concatenate(confs + gconf))
with open(f'w14_cert2_{r0}.cnf.tmp', 'w') as fh:
    fh.write(f'p cnf {NT} {NB + len(keys) + 1}\n')
    for k in range(NB): fh.write(' '.join(str(int(i) + 1) for i in np.nonzero(AV[:, k])[0]) + ' 0\n')
    for kk in keys.tolist(): fh.write(f'-{kk // NT + 1} -{kk % NT + 1} 0\n')
    fh.write(f'{r0 + 1} 0\n')
os.replace(f'w14_cert2_{r0}.cnf.tmp', f'w14_cert2_{r0}.cnf')
with open(f'w14_cert2_{r0}.drat.tmp', 'w') as fh:
    for i in GL: fh.write(f'-{i + 1} 0\n')
    rl = open(rootf).read().splitlines()
    fh.write('\n'.join(rl[:-2]) + ('\n' if len(rl) > 2 else ''))     # root eliminations
    for i in range(len(br)): fh.write(open(f'{D}/child{i}.drat').read())
    fh.write('\n'.join(rl[-2:]) + '\n')
os.replace(f'w14_cert2_{r0}.drat.tmp', f'w14_cert2_{r0}.drat')
print('ASSEMBLED case', r0, 'conf clauses', len(keys), 'nodes this run', stats, round(time.time() - t0), flush=True)
open(f'w14_cert2_{r0}.done', 'w').write('ok\n')
