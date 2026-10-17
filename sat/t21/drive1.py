import sys, time, json
from venn_cegar import solve, min_cover
kmax = int(sys.argv[1]); tl = float(sys.argv[2])
k, pats = 2, []
while k <= kmax:
    t0 = time.time()
    st, sol = solve(k, pats, tl)
    print(f'k={k} {st} {time.time()-t0:.1f}s', flush=True)
    if st != 'SAT':
        break
    cov = min_cover(k, sol)
    print('  sol:', {bin(T)[2:].zfill(k)[::-1]: v for T, v in sorted(sol.items())}, flush=True)
    if cov is None:
        print('  CONFIG HAS TAU>=5: candidate counterexample', flush=True); json.dump({str(T): v for T, v in sol.items()}, open(f'cex_k{k}.json', 'w')); break
    print('  cover:', [(bin(T)[2:].zfill(k)[::-1], mu) for T, mu in cov], flush=True)
    pats.append(cov); k += 1
json.dump([[list(p) for p in pat] for pat in pats], open('pats_drive1.json', 'w'))
