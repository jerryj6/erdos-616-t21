"""solve a DIMACS CNF with a NON-CaDiCaL solver from pysat, write a DRAT proof, run drat-trim.
usage: python3 ref_solve.py CNF SOLVER(glucose4|lingeling|maplechrono) [noproof]"""
import sys, time, subprocess, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'pylib'))
from pysat.formula import CNF
from pysat.solvers import Solver
cnf, name = sys.argv[1], sys.argv[2]
proof = 'noproof' not in sys.argv
t0 = time.time()
F = CNF(from_file=cnf)
print(f'loaded {len(F.clauses)} clauses nv={F.nv} in {time.time()-t0:.1f}s', flush=True)
s = Solver(name=name, bootstrap_with=F.clauses, with_proof=proof); del F
t0 = time.time(); r = s.solve()
print(f'{name}: {"SAT" if r else "UNSAT"} in {time.time()-t0:.1f}s', flush=True)
if r:
    mdl = s.get_model(); open(cnf + '.' + name + '.model', 'w').write(' '.join(map(str, mdl)) + '\n')
elif proof:
    out = cnf + '.' + name + '.drat'
    with open(out, 'w') as f:
        for l in s.get_proof(): f.write(l + '\n')
    s.delete()
    t1 = time.time()
    dt = subprocess.run([os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools', 'drat-trim'), cnf, out],
                        capture_output=True, text=True)
    print('\n'.join(l for l in dt.stdout.splitlines() if l.startswith('s ') or 'erif' in l or 'core' in l), flush=True)
    print(f'drat-trim {time.time()-t1:.1f}s', flush=True)
