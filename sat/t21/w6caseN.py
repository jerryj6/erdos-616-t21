"""Case N / non-uniform probe: 0=E1 1=E2 (5-pair), 2=G single type v, 3=H single type w, |A_G&A_H|=a, |C_G&C_H|=c.
Then CEGAR witness edges (min 4-covers).  Usage: python w6caseN.py a c kmax tl"""
import sys
from w6model import *
a, c, kmax, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
fixed = [(B(0,1,2), B(3), '==', 1), (B(0,1,3), B(2), '==', 1), (B(0,1,2,3), 0, '==', 0),
         (B(0,2,3), B(1), '==', a), (B(1,2,3), B(0), '==', c),
         (B(0,2), B(1), '==', 4), (B(0,3), B(1), '==', 4), (B(1,2), B(0), '==', 4), (B(1,3), B(0), '==', 4),
         (B(2,3), B(0,1), '==', 0)]
pats = {}; k = 4
while k <= kmax:
    st, sol, t = solve(k, pats, fixed, tl)
    print(f'a={a} c={c} k={k} {st} {t:.1f}s', flush=True)
    if sol is None: break
    cov = min_cover(k, sol)
    if cov is None: print('  TAU>=5 model sol', show(k, sol)); break
    full = (1 << k) - 1; pats[k] = [(T, full ^ T, mu) for T, mu in cov]; k += 1
if sol is not None: print('  last sol:', show(k if k <= kmax else kmax, sol))
