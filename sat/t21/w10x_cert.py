"""Certificate for an UNSAT w10x_exact checkpoint:
   python3 w10x_cert.py BRANCH TAG [drop=KIND,..] [K=..] [nosolve]
Rebuilds the CNF deterministically (eager part + every lazy instance in w10x_TAG.json), writes w10x_TAG[suffix].cnf,
solves with CaDiCaL 1.5.3 (pysat) writing a DRAT proof, and runs ../tools/drat-trim on it.
drop=KIND removes the lazy instances of that kind (control runs).  K=.. overrides the pool size (control: K below the
KB bound is NOT sound and is only used to show the pool matters)."""
import sys, os, json, time, subprocess
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w10x_exact import Exact, setup
from pysat.solvers import Cadical153
br, TAG = sys.argv[1], sys.argv[2]
opt = dict(f.split('=', 1) for f in sys.argv[3:] if '=' in f)
here = os.path.dirname(os.path.abspath(__file__))
st = json.load(open(os.path.join(here, f'w10x_{TAG}.json')))
o2 = dict(st.get('opt', {})); o2.update({k: v for k, v in opt.items() if k in ('K', 'nedges', 'src')})
names, B, nk, edges, K, Kb = setup(br, o2)
if 'nonk' in sys.argv: nk = False
drop = set(opt.get('drop', '').split(',')) - {''}
suf = ('_nosb' if os.environ.get('W10X_NOSB') else '') + ('_nonk' if 'nonk' in sys.argv else '') + ('_drop-' + '-'.join(sorted(drop)) if drop else '') + (f'_K{K}' if 'K' in opt else '') + (f'_n{opt["nedges"]}' if 'nedges' in opt else '')
tmp = f'/tmp/w10x_{TAG}{suf}.body'
md = Exact(names, B, edges, K, nk, clfile=tmp, solver=False)
keep = [i for i in st['inst'] if i[0].lstrip('X') not in drop]
for ins in keep: md.add_inst(ins)
md.clf.close()
cnf = os.path.join(here, f'w10x_{TAG}{suf}.cnf')
with open(cnf, 'w') as f:
    f.write(f'p cnf {md.top} {md.ncl}\n')
    with open(tmp) as g:
        for line in g: f.write(line)
os.remove(tmp)
print(f'K={K} (KB bound {Kb}, sound={K >= Kb}) instances kept {len(keep)}/{len(st["inst"])} vars={md.top} clauses={md.ncl}', flush=True)
print('clause tags:', json.dumps(md.tags), flush=True)
if 'nosolve' in sys.argv: sys.exit()
t0 = time.time()
clauses = []
with open(cnf) as f:
    next(f)
    for line in f: clauses.append([int(t) for t in line.split()[:-1]])
s = Cadical153(bootstrap_with=clauses, with_proof=True); del clauses
res = s.solve()
print('solve', 'SAT' if res else 'UNSAT', f'{time.time() - t0:.1f}s', flush=True)
if not res:
    with open(cnf + '.drat', 'w') as f:
        for line in s.get_proof(): f.write(line + '\n')
    s.delete()
    t1 = time.time()
    dt = subprocess.run(['timeout', '1100', os.path.join(here, '..', 'tools', 'drat-trim'), cnf, cnf + '.drat'],
                        capture_output=True, text=True)
    print('\n'.join(l for l in dt.stdout.splitlines() if l.startswith('s ') or 'VERIFIED' in l or 'erif' in l), flush=True)
    print(f'drat-trim {time.time() - t1:.1f}s', flush=True)
