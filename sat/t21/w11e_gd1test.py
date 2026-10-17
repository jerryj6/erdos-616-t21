# quick test: GD1 instances on stored master solutions are detected, encoded, and the encoding agrees with holds_gd1
import sys, json, random
sys.path.insert(0, '.'); sys.path.insert(0, '../pylib')
import w11_benders as WB, w11e_oracle as EO
from w11e_recheck import holds_gd1, check_gd1, BASE
from pysat.solvers import Minisat22
meta = json.load(open('w11_meta2.json')); names, base = WB.setup(meta); bvars = [s['b'] for s in meta['slots']]
rng = random.Random(1); tot = 0; ag = 0
for fn, tag in (('w11e_C_lastsol.json', 'C'), ('w11s_A_lastsol.json', 'A'), ('w11e_B_stall.json', 'B')):
    d = json.load(open(fn)); l2f = d['full']; b = [0] * 24
    for l, f in enumerate(l2f): b[f] = d['b'][l]
    inst = EO.gd1_instances(b, base, 24); inst = [i for i in inst if i[2] in l2f and i[3] in l2f]
    print(fn, 'GD1 violations', len(inst))
    for ins in inst[:20]:
        kind, k, F, L = ins
        rec = dict(generic=dict(kind=kind, k=k, F=F, L=L), traces={str(X): [a for a in range(61) if b[X] >> a & 1] for X in (F, L)})
        check_gd1(rec); enc = WB.PEnc(meta['top'], meta['T']); cl = EO.encode_gd1(enc, ins, bvars, base)
        s = Minisat22(bootstrap_with=enc.cl + [cl, [meta['T']]])
        for t in range(10):
            bb = {X: frozenset(a for a in range(61) if b[X] >> a & 1) for X in range(24)}
            for _ in range(rng.randint(0, 5)):
                X = rng.choice([F, L]); a = rng.choice(sorted(BASE[k])) if rng.random() < .7 else rng.randrange(61); bb[X] = bb[X] ^ {a}
            sem = holds_gd1(rec, bb); ass = [bvars[X][a] if a in bb[X] else -bvars[X][a] for X in (F, L) for a in range(61)]
            assert s.solve(assumptions=ass) == sem, ('MISMATCH', ins, t); tot += 1; ag += sem
        s.delete()
print('GD1 encoder test agree', tot, '(holds', ag, ')')
