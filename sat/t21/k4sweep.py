import sys, itertools, time
from k4model import solve, show
from k4wit import single_patterns, topat
tt = tuple(int(x) for x in sys.argv[1].split(',')); size = int(sys.argv[2]); tl = float(sys.argv[3])
sp = single_patterns(tt); names = sorted(sp)
for combo in itertools.combinations_with_replacement(names, size):
    pats = {4 + i: topat(sp[n]) for i, n in enumerate(combo)}
    st, sol, t, tb = solve(4 + size, tt, pats, tl=tl)
    if st != 'OPTIMAL' and st != 'FEASIBLE' or size == 1:
        print(combo, st, f'{t:.1f}', flush=True)
print('done', flush=True)
