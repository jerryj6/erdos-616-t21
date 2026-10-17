r"""Wave 11 certificate for a sub-instance TAG: CNF = w11s_TAG_base.cnf (w8sat master on the selected singles, +TT +SB
+ eager L4A) + w11s_TAG_allcuts.cnf (all applicable Benders cuts re-encoded from w11b_certs/, w11_sub.py dump).
CaDiCaL 1.5.3 (pysat) with DRAT, then ../tools/drat-trim.   python3 w11s_cert.py TAG [nocuts]  (nocuts = control)"""
import sys, os, time, subprocess, hashlib
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
from pysat.solvers import Cadical153
tag = sys.argv[1]; ctrl = 'nocuts' in sys.argv
out = os.path.join(HERE, f'w11s_{tag}_final{"_nocuts" if ctrl else ""}.cnf')
cl = []; nv = 0
for fn in [f'w11s_{tag}_base.cnf'] + ([] if ctrl else [f'w11s_{tag}_allcuts.cnf']):
    with open(os.path.join(HERE, fn)) as f:
        for line in f:
            if line[0] in 'pc': continue
            v = list(map(int, line.split()))[:-1]
            if v: cl.append(v); nv = max(nv, max(abs(x) for x in v))
with open(out, 'w') as f:
    f.write(f'p cnf {nv} {len(cl)}\n')
    for c in cl: f.write(' '.join(map(str, c)) + ' 0\n')
print(f'{os.path.basename(out)}: p cnf {nv} {len(cl)}', flush=True)
t = time.time(); s = Cadical153(bootstrap_with=cl, with_proof=not ctrl); del cl
r = s.solve(); print('solve', 'SAT' if r else 'UNSAT', f'{time.time()-t:.1f}s', flush=True)
if not r and not ctrl:
    with open(out + '.drat', 'w') as f:
        for line in s.get_proof(): f.write(line + '\n')
    s.delete(); t1 = time.time()
    dt = subprocess.run(['timeout', '1100', os.path.join(HERE, '..', 'tools', 'drat-trim'), out, out + '.drat'], capture_output=True, text=True)
    print('\n'.join(l for l in dt.stdout.splitlines() if l.startswith('s ') or 'verified' in l.lower() or 'error' in l.lower()))
    print(f'drat-trim {time.time()-t1:.1f}s', flush=True)
    for fn in (out, out + '.drat'): print('sha256', os.path.basename(fn), hashlib.sha256(open(fn, 'rb').read()).hexdigest())
