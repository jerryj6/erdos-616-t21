r"""Per-certificate control of the EXTENDED cut encoder (w11e_oracle.encode_cut): for each certificate in w11e_certs/,
encode it alone with a fresh encoder (full slot indexing of w11_meta2.json), fix every edge bit to traces bb = stored b*
perturbed by 0..6 random flips (half of them inside base edges P_k, to exercise the 5-pair condition literals), and check
   CNF satisfiable  <=>  w11e_recheck.holds(cert, bb)   (independent frozenset semantics).
python3 w11e_enctest.py [N=all] [seed]"""
import sys, os, json, glob, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
import w11_benders as WB, w11e_oracle as EO
from w11e_recheck import holds, BASE
from pysat.solvers import Minisat22
from fractions import Fraction
meta = json.load(open(os.path.join(HERE, 'w11_meta2.json'))); names, base = WB.setup(meta); bvars = [s['b'] for s in meta['slots']]
files = sorted(glob.glob(os.path.join(HERE, 'w11e_certs', 'c*.json')))
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
N = min(int(sys.argv[1]), len(files)) if len(sys.argv) > 1 and sys.argv[1] != 'all' else len(files)
def nk(k, key):
    if k == 'L': return (tuple(key[0]), tuple(key[1]))
    return tuple(key)
ns = nu = 0; ncert = 0
for p in rng.sample(files, N):
    rec = json.load(open(p)); enc = WB.PEnc(meta['top'], meta['T'])
    if rec.get('generic') and rec['generic']['kind'].startswith('GD1'):
        g = rec['generic']; cl = EO.encode_gd1(enc, (g['kind'], g['k'], g['F'], g['L']), bvars, base)
    elif rec.get('generic'):
        g = rec['generic']; cl = WB.encode_gen(enc, (g['kind'], tuple(rec['gen_E']), g['mid'], tuple(g['Bp'])), bvars, base)
        sem_fn = None
    else:
        c = dict(E=rec['E'], rows=[(k, nk(k, key), r, Fraction(y)) for k, key, r, y in rec['rows']], kap={int(F): Fraction(v) for F, v in rec['kap'].items()})
        bs = [0] * 24
        for F, v in rec['traces'].items(): bs[int(F)] = sum(1 << a for a in v)
        cl = EO.encode_cut(enc, c, bs, bvars, base)
    s = Minisat22(bootstrap_with=enc.cl + [cl, [meta['T']]]); E = rec['E']; ncert += 1
    for t in range(10):
        bb = {F: frozenset() for F in range(24)}
        for F, v in rec['traces'].items(): bb[int(F)] = frozenset(v)
        for _ in range(rng.randint(0, 6)):
            F = rng.choice(E)
            a = rng.choice(sorted(BASE[rng.randrange(4)])) if rng.random() < 0.5 else rng.randrange(61)
            bb[F] = bb[F] ^ {a}
        if rec.get('generic') and rec['generic']['kind'].startswith('GD1'):
            from w11e_recheck import holds_gd1; sem = holds_gd1(rec, bb)
        elif rec.get('generic'):
            from w11b_recheck import holds as hold_old; sem = hold_old(rec, bb)
        else: sem = holds(rec, bb)
        ass = [bvars[F][a] if a in bb[F] else -bvars[F][a] for F in E for a in range(61)]
        assert s.solve(assumptions=ass) == sem, ('MISMATCH', p, t, sem)
        ns += sem; nu += (not sem)
    s.delete()
print(f'w11e per-certificate encoder control: {ncert} certificates x 10 trace vectors, all agree ({ns} SAT/holds, {nu} UNSAT/violated)')
