r"""Wave 11: final certificate.  CNF = w11_base.cnf (w8sat master, '3211', 24 singles, +TT [+SB]) + w11b_cuts.cnf
(Benders cuts + their aux definitions).  Solve with CaDiCaL 1.5.3 (pysat) writing DRAT, run ../tools/drat-trim.
python3 w11b_cert.py OUT.cnf [nosb]   (nosb: use w11_base_nosb.cnf instead, built by w11b_nosb_prep)"""
import sys, os, time, subprocess, hashlib
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
from pysat.solvers import Cadical153
out = sys.argv[1]; basef = 'w11_base_nosb.cnf' if 'nosb' in sys.argv else 'w11_base.cnf'
skipcuts = 'nocuts' in sys.argv
cl = []; nv = 0
for fn in [basef] + ([] if skipcuts else ['w11b_cuts.cnf']):
    with open(os.path.join(HERE, fn)) as f:
        for line in f:
            if line[0] in 'pc': continue
            v = list(map(int, line.split()))[:-1]
            if v: cl.append(v); nv = max(nv, max(abs(x) for x in v))
with open(out, 'w') as f:
    f.write(f'p cnf {nv} {len(cl)}\n')
    for c in cl: f.write(' '.join(map(str, c)) + ' 0\n')
print(f'{out}: p cnf {nv} {len(cl)}', flush=True)
t = time.time(); s = Cadical153(bootstrap_with=cl, with_proof=True); del cl
r = s.solve(); print('solve', 'SAT' if r else 'UNSAT', f'{time.time()-t:.1f}s', flush=True)
if not r:
    with open(out + '.drat', 'w') as f:
        for line in s.get_proof(): f.write(line + '\n')
    s.delete()
    t1 = time.time()
    dt = subprocess.run(['timeout', '1100', os.path.join(HERE, '..', 'tools', 'drat-trim'), out, out + '.drat'], capture_output=True, text=True)
    print('\n'.join(l for l in dt.stdout.splitlines() if l.startswith('s ') or 'verified' in l.lower() or 'error' in l.lower()))
    print(f'drat-trim {time.time()-t1:.1f}s', flush=True)
    for fn in (out, out + '.drat'):
        h = hashlib.sha256(open(fn, 'rb').read()).hexdigest(); print('sha256', os.path.basename(fn), h)
