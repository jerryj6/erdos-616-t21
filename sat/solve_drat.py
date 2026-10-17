"""Solve a DIMACS CNF with CaDiCaL (pysat cadical153); if UNSAT write DRAT proof to <cnf>.drat"""
import sys, time
from pysat.formula import CNF
from pysat.solvers import Solver
path = sys.argv[1]
t0 = time.time()
cnf = CNF(from_file=path)
print('loaded', len(cnf.clauses), 'clauses', cnf.nv, 'vars', f'{time.time()-t0:.1f}s', flush=True)
with Solver(name='cadical153', bootstrap_with=cnf.clauses, with_proof=True) as s:
    res = s.solve()
    print('result', 'SAT' if res else 'UNSAT', f'{time.time()-t0:.1f}s', flush=True)
    if res:
        m = s.get_model()
        open(path + '.model', 'w').write(' '.join(str(x) for x in m if x > 0) + '\n')
    else:
        pr = s.get_proof()
        with open(path + '.drat', 'w') as f:
            for line in pr:
                f.write(line + '\n')
        print('proof lines', len(pr), flush=True)
