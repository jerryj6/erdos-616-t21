"""End-to-end soundness control of the elimination machinery on literal realizations.
A realization R (base + non-base edges, literally verified) satisfies CONF (all its trace pairs are non-conflicting) and the
cover clauses of exactly those needed B that some non-base edge of R avoids. Run the elimination rule (w14_gac/w14_tree)
on Phi_R = COV(those B) + CONF from alive = all traces: no trace of R may ever be eliminated, and no wipeout may occur.
Also checks the trace-level CONF directly on R. Usage: python3 w14_realtest.py FILE..."""
import sys, json, itertools, numpy as np
sys.path.insert(0, '..')
from w13_enum import P, n, nm, W8
idx = {s: a for a, s in enumerate(W8)}
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T); Cp = z['C']
def crow(rows): return np.unpackbits(Cp[rows], axis=1)[:, :NT].astype(bool)
LUT = {int(t): i for i, t in enumerate(T)}
Bs = [sum(1 << a for a in c) for c in itertools.combinations(range(n), 4)]
need = np.array([B for B in Bs if not any((P[i] & B) == 0 for i in range(4))], dtype=np.int64)
for f in sys.argv[1:]:
    d = json.load(open('../' + f)); names = d.get('names') or d.get('named')
    tr = set()
    for lab, e in zip(d['labels'], d['edges']):
        if lab in ('B0','B1','B2','B3','P0','P1','P2','P3'): continue
        Sn = [(names[x] if x < len(names) else 'U') if isinstance(x, int) else x for x in e]
        tr.add(sum(1 << idx[s] for s in Sn if s in idx))
    Ri = np.array(sorted(LUT[t] for t in tr))
    confR = crow(Ri)[:, Ri].any()
    needR = np.array([B for B in need if any((B & t) == 0 for t in tr)], dtype=np.int64)
    AV = ((T[:, None] & needR[None, :]) == 0)
    alive = np.ones(NT, bool); rnd = 0; bad = False
    while True:
        rnd += 1
        V = (AV & alive[:, None]).astype(np.float32); tot = V.sum(0)
        if (tot == 0).any(): print(f, 'WIPEOUT (unsound!)'); bad = True; break
        dead = np.zeros(NT, bool)
        for a in range(0, NT, 1500):
            comp = (~crow(np.arange(a, min(a + 1500, NT)))).astype(np.float32)
            s = comp @ V
            dead[a:a+1500] = ((s < 0.5) & ~AV[a:a+1500]).any(1) & alive[a:a+1500]
        if not dead.any(): break
        alive &= ~dead
        if not alive[Ri].all(): print(f, 'REALIZATION TRACE ELIMINATED (unsound!)', rnd); bad = True; break
    print(f, 'traces', len(Ri), 'CONF violated' if confR else 'CONF ok', 'needR', len(needR), 'rounds', rnd,
          'alive', int(alive.sum()), 'R survives' if not bad else 'FAIL', flush=True)
