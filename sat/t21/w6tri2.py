import sys, json
from w6fast import solve
from w6model import B, show, min_cover
r = int(sys.argv[1]); tl = float(sys.argv[2]); guide = sys.argv[3]; kmax = int(sys.argv[4]) if len(sys.argv) > 4 else 0; mf = int(sys.argv[5]) if len(sys.argv) > 5 else 99
P = {21: dict(r=21, K=5, W=60), 16: dict(r=16, K=4, W=45)}[r]; K = P['K']; R = P['r']
# triangle: 0=Q(E1) 1=P1(E2) 2=P2(G) 3=P3(H)
basesz = {B(0): R-3*(K-2)-3, B(1): R-K-1-(K-2)-1+0, B(2): 0, B(3): 0,
          B(0,1): K-2, B(0,2): K-2, B(0,3): K-2, B(0,1,2): 1, B(0,1,3): 1, B(0,2,3): 1, B(1,2,3): K-1, 0: 0}
for i in (1, 2, 3): basesz[B(i)] = R - (K-1) - 2 - (K-2)
x12, x13, x23, C0 = (B(0,1,2), B(3)), (B(0,1,3), B(2)), (B(0,2,3), B(1)), (B(1,2,3), B(0))
Q1, Q2, Q3, Qs = (B(0,1), B(2,3)), (B(0,2), B(1,3)), (B(0,3), B(1,2)), (B(0), B(1,2,3))
G = {'J': [(*C0, 4)],
     'Y12': [(*x12, 1), (*C0, 3)], 'Y13': [(*x13, 1), (*C0, 3)], 'Y23': [(*x23, 1), (*C0, 3)],
     'Z1': [(*x12, 1), (*x13, 1), (*C0, 2)], 'Z2': [(*x12, 1), (*x23, 1), (*C0, 2)], 'Z3': [(*x13, 1), (*x23, 1), (*C0, 2)],
     'D': [(*x12, 1), (*x13, 1), (*x23, 1), (*C0, 1)]}
if K == 4:  # r=16 analogue: C0 has 3 points
    G = {'J': [(*C0, 3)], 'Y12': [(*x12, 1), (*C0, 2)], 'Y13': [(*x13, 1), (*C0, 2)], 'Y23': [(*x23, 1), (*C0, 2)],
         'Z1': [(*x12, 1), (*x13, 1), (*C0, 1)], 'Z2': [(*x12, 1), (*x23, 1), (*C0, 1)], 'Z3': [(*x13, 1), (*x23, 1), (*C0, 1)],
         'D': [(*x12, 1), (*x13, 1), (*x23, 1)]}
pats = {}; k = 4
for name in guide.split(','):
    if name: pats[k] = G[name]; k += 1
while True:
    st, sol, t, tb = solve(k, 4, basesz, pats, tl, maxfam=mf, **P)
    print(f'r={r} k={k} guide={guide} {st} {t:.1f}s (build {tb:.1f}s)', flush=True)
    if sol is None or k >= kmax: 
        if sol: print('  sol:', show(k, sol), flush=True)
        break
    cov = min_cover(k, sol); print('  sol:', show(k, sol), flush=True)
    if cov is None: print('  TAU>=5 model solution'); break
    full = (1 << k) - 1; pats[k] = [(T, full ^ T, mu) for T, mu in cov]
    print('  cover ->', [(bin(T)[2:].zfill(k)[::-1], mu) for T, mu in cov], flush=True); k += 1
