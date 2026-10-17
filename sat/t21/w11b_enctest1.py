r"""Per-certificate semantic control of the cut encoder: encode ONE certificate (fresh encoder, full slot indexing of
w11_meta2.json), fix all edge bits to traces bb (stored b* perturbed by 0..6 random flips on the cut's own edges), and
check  CNF SAT  <=>  w11b_recheck.holds(cert, bb)  (independent set-based semantics)."""
import sys, os, json, glob, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
from w11b_recheck import holds
import w11_benders as WB
from pysat.solvers import Minisat22
meta = json.load(open(os.path.join(HERE, 'w11_meta2.json'))); names, base = WB.setup(meta); bvars = [s['b'] for s in meta['slots']]
files = glob.glob(os.path.join(HERE, 'w11b_certs', 'c*.json')); rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 60; ns = nu = 0
for p in rng.sample(files, N):
    rec = json.load(open(p)); enc = WB.PEnc(meta['top'], meta['T'])
    if rec.get('generic'):
        g = rec['generic']; cl = WB.encode_gen(enc, (g['kind'], tuple(rec['gen_E']), g['mid'], tuple(g['Bp'])), bvars, base)
    else:
        c, bs = WB.cert_to_internal(rec); bfull = [0] * 24
        for F, v in bs.items(): bfull[F] = v
        cl = WB.encode_cut(enc, c, bfull, bvars, base)
    s = Minisat22(bootstrap_with=enc.cl + [cl, [meta['T']]])
    E = rec['E']
    for t in range(8):
        bb = {F: frozenset() for F in range(24)}
        for F, v in rec['traces'].items(): bb[int(F)] = frozenset(v)
        for _ in range(rng.randint(0, 6)):
            F = rng.choice(E); a = rng.randrange(61); bb[F] = bb[F] ^ {a}
        sem = holds(rec, bb)
        ass = [bvars[F][a] if a in bb[F] else -bvars[F][a] for F in E for a in range(61)]
        assert s.solve(assumptions=ass) == sem, ('MISMATCH', p, t)
        ns += sem; nu += (not sem)
    s.delete()
print(f'per-certificate encoder control: {N} certificates x 8 trace vectors, all agree ({ns} SAT/holds, {nu} UNSAT/violated)')
