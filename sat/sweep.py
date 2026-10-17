"""Sweep partition shapes for typesearch. Usage: python sweep.py p nmin nmax [r K tlim]"""
import sys, time, signal
from typesearch import run

def parts(n, p, mn=1):
    if p == 1:
        if n >= mn: yield (n,)
        return
    for a in range(mn, n // p + 1):
        for rest in parts(n - a, p - 1, a):
            yield (a,) + rest

class TO(Exception): pass
def handler(s, f): raise TO()
signal.signal(signal.SIGALRM, handler)

p, nmin, nmax = map(int, sys.argv[1:4])
r = int(sys.argv[4]) if len(sys.argv) > 4 else 21
K = int(sys.argv[5]) if len(sys.argv) > 5 else 5
tlim = int(sys.argv[6]) if len(sys.argv) > 6 else 600
out = open(f'sweep_p{p}_r{r}_K{K}_{nmin}-{nmax}.txt', 'a')
for n in range(nmin, nmax + 1):
    for al in parts(n, p):
        t0 = time.time()
        signal.alarm(tlim)
        try:
            res, ch = run(r, K, list(al), verbose=False)
        except TO:
            res, ch = 'TIMEOUT', None
        signal.alarm(0)
        line = f'{al} {res} {ch} {time.time()-t0:.1f}s'
        out.write(line + '\n'); out.flush()
        if res == 'SAT':
            print('FOUND', line, flush=True)
