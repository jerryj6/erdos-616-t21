"""(hedge) symmetry case split with SMALL per-case certificates.
Root: B* = a needed 4-set with fewest avoiders. Stab(B*) ⊆ base group (tr_sym). Every model has an avoider t of B*;
by the semantic WLOG (tr_sym docstring) it suffices to refute Φ ∧ x_r for one r per Stab(B*)-orbit of avoiders of B*.
Per case r: propagate x_r (neighbours false), positive units (a COV with one live literal) and the RUP elimination rule
to a fixpoint, recording every derived unit with its justification. The case CNF is a SUBSET of Φ's clauses plus the
unit x_r: COV (all) + the binary CONF clauses used by the justifications + CONF among the still-alive traces. The DRAT
is: derived units (in order, each RUP), then kissat's text proof of (case CNF + those units), or the empty clause on wipeout.
usage: python3 tr_case.py TAG plan | case K"""
import sys, os, json, itertools, subprocess, numpy as np
from tr_sym import gens, group, apply
tag = sys.argv[1]; a, c = int(tag[0]), int(tag[1])
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; NT = len(tr); n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
pairs = np.load(f'pairs_{tag}.npy')
C = np.zeros((NT, NT), bool); C[pairs[:, 0], pairs[:, 1]] = True; C |= C.T
need = [B for B in (sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))]
av = [np.nonzero((tr & B) == 0)[0] for B in need]
def plan():
    k = min(range(len(need)), key=lambda i: len(av[i])); Bs = need[k]
    names, Pm, OS, G = gens(a, c); E = group(G, n)
    stab = [e for e in E if apply(e, Bs) == Bs]
    lut = {int(t): i for i, t in enumerate(tr)}
    seen = set(); reps = []
    for t in av[k].tolist():
        if t in seen: continue
        orb = {lut[apply(e, int(tr[t]))] for e in stab}; seen |= orb; reps.append((t, len(orb)))
    assert seen == set(av[k].tolist())
    json.dump({'Bstar': Bs, 'avoiders': av[k].tolist(), 'stab': len(stab), 'reps': reps}, open(f'case_{tag}_plan.json', 'w'))
    print('B*', [names[x] for x in range(n) if Bs >> x & 1], 'avoiders', len(av[k]), '|Stab|', len(stab), 'orbits', len(reps))
def case(K):
    pl = json.load(open(f'case_{tag}_plan.json')); r = pl['reps'][K][0]; name = f'case_{tag}_{K}'
    alive = np.ones(NT, bool); val = np.zeros(NT, np.int8)   # +1 true, -1 false
    units = []; just = set()
    def settrue(t):
        val[t] = 1
        for s in np.nonzero(C[t] & alive & (val == 0))[0]:
            val[s] = -1; alive[s] = False; units.append(-(s + 1)); just.add((min(t, s), max(t, s)))
    settrue(r); ch = True
    while ch:
        ch = False
        for k in range(len(need)):
            A = av[k][alive[av[k]]]
            if len(A) == 0:
                units.append(0); break
            if (val[A] == 1).any(): continue
            if len(A) == 1:
                units.append(int(A[0]) + 1); settrue(int(A[0])); ch = True; continue
            X = C[A].all(axis=0) & alive & (val == 0); X[av[k]] = False
            for t in np.nonzero(X)[0]:
                alive[t] = False; val[t] = -1; units.append(-(t + 1)); ch = True
                for s in A: just.add((min(t, s), max(t, s)))
        if units and units[-1] == 0: break
    wipe = bool(units) and units[-1] == 0
    al = np.nonzero(alive & (val == 0))[0]
    conf = set(just)
    if not wipe:
        sub = C[np.ix_(al, al)]; ii, jj = np.nonzero(np.triu(sub, 1))
        conf |= {(int(al[i]), int(al[j])) for i, j in zip(ii, jj)}
    # trues also need their CONF with alive vars (already in just via settrue); write CNF
    with open(name + '.cnf', 'w') as fh:
        fh.write(f'p cnf {NT} {len(need) + 1 + len(conf)}\n')
        for A in av: fh.write(' '.join(str(x + 1) for x in A) + ' 0\n')
        fh.write(f'{r + 1} 0\n')
        for s, t in conf: fh.write(f'-{s + 1} -{t + 1} 0\n')
    print(name, 'r', r, 'derived units', len([u for u in units if u]), 'wipeout', wipe, 'alive', len(al), 'CONF in case CNF', len(conf), flush=True)
    if wipe:
        with open(name + '.drat', 'w') as fh:
            for u in units[:-1]: fh.write(f'{u} 0\n')
            fh.write('0\n')
        return
    with open(name + '.u.cnf', 'w') as fh:   # case CNF + derived units (for kissat)
        body = open(name + '.cnf').read().split('\n', 1)[1]
        uu = [u for u in units if u]
        fh.write(f'p cnf {NT} {len(need) + 1 + len(conf) + len(uu)}\n' + body)
        for u in uu: fh.write(f'{u} 0\n')
    rc = subprocess.run(f'taskset -c 0 nice -n 10 ../../tools/kissat -q --binary=false --time=1100 {name}.u.cnf {name}.kdrat', shell=True).returncode
    print(name, 'kissat rc', rc, flush=True)
    if rc == 20:
        with open(name + '.drat', 'w') as fh:
            for u in units:
                if u: fh.write(f'{u} 0\n')
            fh.write(open(name + '.kdrat').read())
        os.remove(name + '.kdrat'); os.remove(name + '.u.cnf')
if __name__ == '__main__':
    if sys.argv[2] == 'plan': plan()
    else: case(int(sys.argv[3]))
