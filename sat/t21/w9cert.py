"""Certificate for an UNSAT w9run checkpoint: python3 w9cert.py BRANCH TAG [drop=KIND,KIND] [nosolve]
Rebuilds the CNF deterministically from w9_TAG.json (edges + lazy instances), writes w9_TAG[_ctrl].cnf and a tag
histogram (which lemma each clause instantiates), solves with CaDiCaL + DRAT proof, runs drat-trim.
drop=KIND removes every lazy instance of that kind (control runs: shows the kind is needed)."""
import sys, json, subprocess, time, os
from w9lazy import *
br, TAG = sys.argv[1], sys.argv[2]
opt = dict(f.split('=', 1) for f in sys.argv[3:] if '=' in f)
drop = set(opt.get('drop', '').split(',')) - {''}
dropE = set(opt.get('dropedge', '').split(',')) - {''}
if br.startswith('k4:'): names, B = base_k4(br[3:]); nk = False
else: a, c = map(int, br[5:].split(',')); names, B = base_nok4(a, c); nk = True
suf = ('_drop-' + '-'.join(sorted(drop)) if drop else '') + ('_dropgen-' + '-'.join(sorted(dropE)) if dropE else '')
clf = f'/tmp/w9_{TAG}{suf}.cl'
md = Model(names, B, nk=nk, flags=[f'clfile={clf}'])
del md.solver   # build only
md.add = Model.add.__get__(md)
st = json.load(open(f'w9_{TAG}.json'))
for e in st['edges']: md.add_edge(e['avoid'], e['gen'], e['label'])
src = json.load(open(opt['core']))['inst'] if 'core' in opt else st['inst']
keep = [ins for ins in src if ins[0] not in drop]
if 'core' in opt: suf += '_core'
if dropE:
    bad = {i for i, e in enumerate(st['edges']) if str(e['gen']) in dropE}
    def uses(ins): return any(isinstance(t, int) and t in bad for t in ins[1:]) or any(isinstance(t, list) and set(t) & bad for t in ins[1:] if ins[0] in ('TT', 'CAP'))
    keep = [ins for ins in keep if not uses(ins)]
for ins in keep: md.add_inst(ins)
md.clf.close()
cnf = f'w9_{TAG}{suf}.cnf'
with open(cnf, 'w') as f:
    f.write(f'p cnf {md.top} {md.ncl}\n')
    for line in open(clf):
        f.write(line.split(' ', 1)[1].rstrip('\n') + ' 0\n' if ' ' in line.strip() else '0\n')
print('instances kept', len(keep), 'of', len(st['inst']), 'edges', len(md.edges), 'vars', md.top, 'clauses', md.ncl, flush=True)
print('clause tags:', json.dumps(md.tagcount), flush=True)
if 'nosolve' in sys.argv: sys.exit()
t0 = time.time()
r = subprocess.run(['timeout', '1000', 'cadical', '--no-binary', cnf, cnf + '.drat'], capture_output=True, text=True) if subprocess.run(['which', 'cadical'], capture_output=True).returncode == 0 else None
if r is None:
    from pysat.formula import CNF
    from pysat.solvers import Cadical153
    F = CNF(from_file=cnf)
    s = Cadical153(bootstrap_with=F.clauses, with_proof=True)
    res = s.solve()
    print('solve', 'SAT' if res else 'UNSAT', f'{time.time()-t0:.1f}s', flush=True)
    if not res:
        with open(cnf + '.drat', 'w') as f:
            for line in s.get_proof(): f.write(line + '\n')
        dt = subprocess.run(['timeout', '1100', '../tools/drat-trim', cnf, cnf + '.drat'], capture_output=True, text=True)
        print('\n'.join(l for l in dt.stdout.splitlines() if l.startswith('s ') or 'VERIFIED' in l or 'verif' in l.lower())[:2000], flush=True)
