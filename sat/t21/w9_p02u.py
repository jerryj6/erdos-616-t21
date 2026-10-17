r"""Wave 9: is '(P0,P2) uniform' compatible with the (3,2,1,1)-K4 at first-generation depth?
= a LOCAL test of propagation lemma (P): (X,Y)=(P0,P2) uniform, F=P1 its type-v single, and P3 is a type-w single of
(X,F)=(P0,P1) with (k,c)=(2,3), i.e. (X,F) non-uniform.  We take the Wave-8 CNF model w8sat.build (all 24 first-gen
witnesses, flags from argv) and FORCE every (0,2)-single in the model to have the same parts as P1:
F∩(P0\N02) = M\{v} = T013 ∪ p01,   F∩(P2\N02) = γ ∪ c3 = T123 ∪ p12.   SAT => (P) is locally consistent-false here."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import w8sat
from pysat.solvers import Cadical153
from pysat.formula import CNF
flags = sys.argv[1:]
def extra(e, X, pts, P, N):
    for F in X:
        if F['pair'] != (0, 2): continue
        for a in range(len(pts)):
            name, mem = pts[a]
            if a in N[0, 2]: continue
            if 0 in mem and 2 not in mem or 2 in mem and 0 not in mem or (0 in mem and 2 in mem):
                want = name.startswith('T013') or name.startswith('p01') or name.startswith('T123') or name.startswith('p12')
                e.cl.append([F['b'][a]] if want else [-F['b'][a]])
t0 = time.time()
import json
gen = next((json.loads(f.split('=',1)[1]) for f in flags if f.startswith('gens=')), [])
e, X, pts, W = w8sat.build('3211', None, gen=[tuple(g) for g in gen], U='U' in flags, tt='tt' in flags, extra=extra)
print('built', len(e.cl), 'clauses', f'{time.time()-t0:.0f}s', flush=True)
cnf = next((f.split('=')[1] for f in flags if f.startswith('cnf=')), None)
if cnf: CNF(from_clauses=e.cl).to_file(cnf)
s = Cadical153(bootstrap_with=e.cl, with_proof='drat' in flags)
r = s.solve(); print('SAT' if r else 'UNSAT', f'{time.time()-t0:.0f}s', flush=True)
if r:
    m = set(l for l in s.get_model() if l > 0)
    for F in X: print(F['pair'], pts[F['x']][0] if F['x'] is not None else F.get('gen'), [pts[a][0] for a in range(len(pts)) if F['b'][a] in m], flush=True)
elif 'drat' in flags:
    with open(cnf + '.drat', 'w') as f:
        for line in s.get_proof(): f.write(line + '\n')
