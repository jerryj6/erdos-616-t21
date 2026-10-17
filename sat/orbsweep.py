import sys, time, os
from orbitsat import run
import numpy as np
SMAX = int(os.environ.get('SMAX', '99'))
to = float(sys.argv[1])
for spec in sys.argv[2:]:
    n, g = spec.split('/'); n = int(n)
    lines = []
    def log(s):
        lines.append(s); print(s, flush=True)
    sm = min(21, n - 4, SMAX)
    try:
        st, S = run(n, 21, 5, 9, sm, g, to, log)
    except Exception as e:
        st, S = 'ERR ' + repr(e), None
    with open('orbsweep_results.txt', 'a') as f:
        f.write(f"{n} {g} smax={sm} {st} | {lines[0] if lines else ''} | {lines[-1] if lines else ''}\n")
    with open('../../candidates/erdos-616-t21-construct.md', 'a') as f:
        f.write(f"* sweep result: n={n} group={g} sizes=[9,{sm}] -> {st} | {lines[-1] if lines else ''}\n")
    if st == 'FOUND':
        np.save(f"FOUND_orbit_n{n}_r21_{g.replace(':','-').replace(',','_')}.npy", S)
