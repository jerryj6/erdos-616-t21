"""Guided witnesses for Case I (triangle). edges 0=E1 1=E2(P1) 2=G(P2) 3=H(P3). Then CEGAR."""
import sys
from w6model import *
r = int(sys.argv[1]); kmax = int(sys.argv[2]); tl = float(sys.argv[3]); guide = sys.argv[4]
P = {21: dict(r=21, K=5, W=60), 16: dict(r=16, K=4, W=45)}[r]; K = P['K']
fixed = []
def g(inc, exc, val): fixed.append((inc, exc, '==', val))
g(B(0,1,2), B(3), 1); g(B(0,1,3), B(2), 1); g(B(0,1), B(2,3), K-2); g(B(0,1,2,3), 0, 0)
g(B(0,2,3), B(1), 1); g(B(0,2), B(1,3), K-2); g(B(0,3), B(1,2), K-2)
g(B(1,2,3), B(0), K-1); g(B(1,2), B(0,3), 0); g(B(1,3), B(0,2), 0); g(B(2,3), B(0,1), 0)
v, w, p, C0 = (B(0,1,2), B(3)), (B(0,1,3), B(2)), (B(0,2,3), B(1)), (B(1,2,3), B(0))
G = {'J': [(*C0, K-1)], 'Yv': [(*v, 1), (*C0, K-2)], 'Yw': [(*w, 1), (*C0, K-2)], 'Yp': [(*p, 1), (*C0, K-2)]}
pats = {}; k = 4
for name in guide.split(','):
    if name: pats[k] = G[name]; k += 1
while k <= kmax:
    st, sol, t = solve(k, pats, fixed, tl, **P)
    print(f'k={k} {st} {t:.1f}s', flush=True)
    if sol is None: break
    print('  sol:', show(k, sol), flush=True)
    cov = min_cover(k, sol)
    if cov is None: print('  TAU>=5 model solution'); break
    full = (1 << k) - 1; pats[k] = [(T, full ^ T, mu) for T, mu in cov]
    print('  cover ->', [(bin(T)[2:].zfill(k)[::-1], mu) for T, mu in cov], flush=True); k += 1
st, sol, t = solve(k, pats, fixed, tl, **P) if k > kmax and False else (None, None, 0)
