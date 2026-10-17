r"""Semantic control of the cut encoding for a sub-instance: for perturbations bb of the master solution, the CNF made
of all re-encoded cuts (w11s_TAG_allcuts.cnf) with edge bits fixed to bb is SAT iff every applicable certificate's
disjunction holds at bb (semantics evaluated independently by w11b_recheck.holds)."""
import sys, os, json, glob, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
from w11b_recheck import holds
from pysat.solvers import Cadical153
tag = sys.argv[1]; ntest = int(sys.argv[2]) if len(sys.argv) > 2 else 40
meta = json.load(open(os.path.join(HERE, f'w11s_{tag}_meta.json'))); l2f = [s['full'] for s in meta['slots']]; f2l = {f: l for l, f in enumerate(l2f)}
bvars = [s['b'] for s in meta['slots']]
certs = [json.load(open(p)) for p in glob.glob(os.path.join(HERE, 'w11b_certs', 'c*.json'))]
certs = [c for c in certs if all(F in f2l for F in c['E'])]
cl = []
with open(os.path.join(HERE, f'w11s_{tag}_allcuts.cnf')) as f:
    for line in f: cl.append(list(map(int, line.split()))[:-1])
s = Cadical153(bootstrap_with=cl + [[meta['T']]])
sol = json.load(open(os.path.join(HERE, f'w11s_{tag}_lastsol.json')))['b']
rng = random.Random(3); nsat = 0
for t in range(ntest):
    c0 = rng.choice(certs)
    bb = {l2f[l]: frozenset(a for a in range(61) if sol[l] >> a & 1) for l in range(len(l2f))}
    for F, v in c0['traces'].items(): bb[int(F)] = frozenset(v)
    for _ in range(rng.randint(0, 3)):
        F = rng.choice(l2f); a = rng.randrange(61); bb[F] = bb[F] ^ {a}
    sem = all(holds(c, bb) for c in certs)
    ass = [bvars[f2l[F]][a] if a in bb[F] else -bvars[f2l[F]][a] for F in l2f for a in range(61)]
    assert s.solve(assumptions=ass) == sem, ('MISMATCH', t)
    nsat += sem
print(f'{tag}: cut-encoding semantic test {ntest}/{ntest} agree ({nsat} all-cuts-satisfied, {ntest-nsat} some cut violated); certs applicable {len(certs)}')
