"""CEGAR driver: python w6cegar.py CASE r kmax tl.   Adds one witness edge per round for a min 4-cover of the
current model solution (exact regions).  Prints UNSAT (=> case closed, modulo soundness) or the last solution."""
import sys, json, time
from w6model import *
case, r, kmax, tl = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
P = {21: dict(r=21, K=5, W=60), 16: dict(r=16, K=4, W=45)}[r]
K = P['K']
pats, fixed, k = {}, [], 2
if case == 'base':
    k = 2
elif case == 'tri':   # Case I triangle: 0=E1 1=E2 2=G 3=H
    k = 4
    def g(inc, exc, val): fixed.append((inc, exc, '==', val))
    g(B(0,1,2), B(3), 1); g(B(0,1,3), B(2), 1); g(B(0,1), B(2,3), K-2); g(B(0,1,2,3), 0, 0)
    g(B(0,2,3), B(1), 1); g(B(0,2), B(1,3), K-2); g(B(0,3), B(1,2), K-2)
    g(B(1,2,3), B(0), K-1); g(B(1,2), B(0,3), 0); g(B(1,3), B(0,2), 0); g(B(2,3), B(0,1), 0)
elif case == 'tri0':  # triangle without fixing (only the defining hypothesis): G,H singles distinct types, |A_G&A_H|=1
    k = 4
    fixed += [(B(0,1,2), 0, '==', 1), (B(0,1,3), 0, '==', 1), (B(0,1,2,3), 0, '==', 0), (B(0,2,3), B(1), '==', 1)]
extra = sys.argv[5] if len(sys.argv) > 5 else ''
log = []
while k <= kmax:
    st, sol, t = solve(k, pats, fixed, tl, **P)
    print(f'k={k} {st} {t:.1f}s', flush=True)
    if sol is None: break
    print('  sol:', show(k, sol), flush=True)
    cov = min_cover(k, sol)
    if cov is None:
        print('  MODEL SOLUTION HAS TAU>=5 as a k-edge hypergraph: check L literally!', flush=True); break
    full = (1 << k) - 1
    pats[k] = [(T, full ^ T, mu) for T, mu in cov]
    print('  cover ->', [(bin(T)[2:].zfill(k)[::-1], mu) for T, mu in cov], flush=True)
    k += 1
json.dump({str(e): p for e, p in pats.items()}, open(f'w6_{case}_{r}_pats.json', 'w'))
