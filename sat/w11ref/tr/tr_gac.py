"""global elimination on Φ_TAG (RUP rule): if every ALIVE avoider of a needed B conflicts with t (t not an avoider of B),
then ¬x_t (unit propagation on COV(B) + CONF + earlier units). Iterate to fixpoint; a needed B with no alive avoider = wipeout.
Writes gac_TAG.json (eliminated traces in order, with witness B) and, on wipeout, gac_TAG.drat (text DRAT: the units, then
the empty clause) for phi_TAG.cnf.   usage: python3 tr_gac.py TAG"""
import sys, itertools, json, numpy as np
tag = sys.argv[1]
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; NT = len(tr); n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
pairs = np.load(f'pairs_{tag}.npy')
C = np.zeros((NT, NT), bool); C[pairs[:, 0], pairs[:, 1]] = True; C |= C.T
need = [B for B in (sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))]
av = [np.nonzero((tr & B) == 0)[0] for B in need]
alive = np.ones(NT, bool); elim = []; wipe = None; rnd = 0
while wipe is None:
    rnd += 1; ch = 0
    for k, B in enumerate(need):
        A = av[k][alive[av[k]]]
        if len(A) == 0: wipe = int(B); break
        X = C[A].all(axis=0) & alive
        X[av[k]] = False
        for t in np.nonzero(X)[0]:
            alive[t] = False; elim.append((int(t), int(B))); ch += 1
    print('round', rnd, 'eliminated', ch, 'alive', int(alive.sum()), flush=True)
    if ch == 0: break
json.dump({'elim': elim, 'wipeout': wipe, 'alive': np.nonzero(alive)[0].tolist()}, open(f'gac_{tag}.json', 'w'))
print('wipeout B', wipe, 'eliminated', len(elim), 'alive', int(alive.sum()))
if wipe is not None:
    with open(f'gac_{tag}.drat', 'w') as fh:
        for t, B in elim: fh.write(f'-{t + 1} 0\n')
        fh.write('0\n')
