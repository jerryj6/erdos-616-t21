"""Control for the w10x encoding (exactness + soundness w.r.t. the literal semantics):
take a model solution S (a literal hypergraph), list the lemma instances it violates (literal checker) and a sample of
instances it satisfies; for each, build a fresh model, add that single instance, and solve with every edge bit FIXED
to S.  Expected: violated -> UNSAT (the clause really excludes S), satisfied -> SAT (the clause does not exclude a
configuration that satisfies the lemma; the aux variables can take their intended values).
usage: python3 w10x_selftest.py BRANCH sel=.. K=.. [n=40]"""
import sys, os, json, itertools, random
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w10x_exact import Exact, setup, check, literal
br = sys.argv[1]; opt = dict(f.split('=', 1) for f in sys.argv[2:] if '=' in f)
names, B, nk, edges, K, Kb = setup(br, opt)
nt = int(opt.get('n', 40)); random.seed(1)
md = Exact(names, B, edges, K, nk)
S = md.solve()
viol = check(md, S, limit=200)
viol = [v for v in viol if v[0] != 'A?']
nb = md.nb; allE = list(range(-nb, 0)) + list(range(len(edges)))
E = literal(md, S)
vk = set(json.dumps(v) for v in viol)
# sample satisfied instances of each kind
sat_inst = []
for _ in range(4000):
    k = random.choice(['L', 'R3', 'SA', 'D1', 'W7', 'TT'])
    if k == 'L': z = ['L', sorted(random.sample(allE, random.choice([3, 4, 5])))]
    elif k in ('R3', 'D1'): z = [k] + random.sample(allE, 3)
    elif k in ('SA', 'W7'): z = [k] + random.sample(allE, 4)
    else:
        x = random.sample(allE, 4); z = ['TT', x[0], x[1:]]
    if all(t < 0 for t in (z[1] if k == 'L' else [t for t in z[1:] if isinstance(t, int)] + (z[2] if k == 'TT' else []))): continue
    key = lambda e: (-1 - e) if e < 0 else nb + e
    if k == 'L': z = ['L', sorted(z[1], key=key)]
    elif k in ('R3', 'D1'): z = [k] + sorted(z[1:3], key=key) + [z[3]]
    elif k in ('SA', 'W7'): z = [k] + sorted(z[1:3], key=key) + z[3:]
    else: z = ['TT', z[1], sorted(z[2], key=key)]
    alts = [z] + ([[k] + z[1:3] + [z[4], z[3]]] if k in ('SA', 'W7') else [])
    if not any(json.dumps(a) in vk for a in alts): sat_inst.append(z)
random.shuffle(viol)
tests = [(v, False) for v in viol[:nt]] + [(z, True) for z in sat_inst[:nt]]
bad = 0; res = {}
for z, expect in tests:
    for form in ('', 'X'):
        m2 = Exact(names, B, edges, K, nk)
        m2.add_inst([form + z[0]] + z[1:])
        assum = [(e['x'][a] if a in S[p] else -e['x'][a]) for p, e in enumerate(m2.edges) for a in range(m2.n)]
        r = m2.solver.solve(assumptions=assum)
        key = (form + z[0], 'viol' if not expect else 'ok')
        res.setdefault(key, [0, 0])[0 if r == expect else 1] += 1
        if r != expect and not (expect is False and form == '' ): bad += 1; print('MISMATCH', form, z, 'expected', expect, 'got', r, flush=True)
        if r != expect and expect is False and form == '': print('counter form not tight (escalation case):', z, flush=True)
print('violated tested', min(nt, len(viol)), 'satisfied tested', min(nt, len(sat_inst)))
print('results {(form,kind),(viol|ok)): [as expected, not]}:', {f'{k[0]}/{k[1]}': v for k, v in sorted(res.items())})
print('SOUNDNESS/EXACTNESS MISMATCHES (excluding tolerated non-tight counter forms):', bad)
