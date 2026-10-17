"""CEGAR on the K4 base: repeatedly find a model solution, pick a <=4-point cover (by regions) of all its edges,
add a new edge avoiding those points (tau>=5).  INFEASIBLE at some k => K4 config with these triples impossible
(in Case N: NT constraint on).  Usage: python k4cegar.py c,a,1,1 kmax tl [guide names comma-sep]"""
import sys, itertools, time
from k4model import solve, show
from k4wit import single_patterns, topat
tt = tuple(int(x) for x in sys.argv[1].split(',')); kmax = int(sys.argv[2]); tl = float(sys.argv[3])
guide = sys.argv[4].split(',') if len(sys.argv) > 4 and sys.argv[4] else []
sp = single_patterns(tt)
def min_cover(k, sol, maxsize=4):
    """a cover by exactly maxsize points (multiset of regions, within region sizes) of all k edges, maximizing the
    total degree (avoiding more points only strengthens the witness edge)."""
    regs = sorted(sol, key=lambda T: -bin(T).count('1'))[:40]; allE = (1 << k) - 1; best = None
    for combo in itertools.combinations_with_replacement(regs, maxsize):
        u = 0
        for T in combo: u |= T
        if u != allE: continue
        cnt = {}
        for T in combo: cnt[T] = cnt.get(T, 0) + 1
        if any(cnt[T] > sol[T] for T in cnt): continue
        score = sum(bin(T).count('1') for T in combo)
        if best is None or score > best[0]: best = (score, sorted(cnt.items()))
    return best[1] if best else None
pats = {}; k = 4
for g in guide: pats[k] = topat(sp[g]); k += 1
while True:
    st, sol, t, tb = solve(k, tt, pats, tl=tl)
    print(f'tt={tt} k={k} {st} {t:.1f}s', flush=True)
    if sol is None or k >= kmax:
        if sol: print('  sol', show(k, sol), flush=True)
        break
    cov = min_cover(k, sol)
    if cov is None: print('  TAU>=5 SOLUTION', show(k, sol)); break
    full = (1 << k) - 1
    pats[k] = [((lambda TT: (lambda T: T == TT))(T & full), mu) for T, mu in cov]
    print('  cover', [(bin(T)[2:].zfill(k)[::-1], mu) for T, mu in cov], flush=True); k += 1
