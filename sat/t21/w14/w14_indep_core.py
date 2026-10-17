"""Independent re-check (w14_indep.feasible_pair, exhaustive overlap enumeration, no shared code with w14_compat) of EVERY
binary conflict clause in a drat-trim core file. Resumable: progress in <core>.indep.json. Usage: python3 w14_indep_core.py CORE"""
import sys, os, json, time
from w14_indep import feasible_pair
import numpy as np
core = sys.argv[1]; PF = core + '.indep.json'
ST = {b: s for b, s in json.load(open('w14_states.json'))}
T = np.load('w14_conf.npz')['T']
pairs = []
for line in open(core):
    if line[0] in 'pc': continue
    L = [int(x) for x in line.split()[:-1]]
    if len(L) == 2 and L[0] < 0 and L[1] < 0: pairs.append((-L[0] - 1, -L[1] - 1))
st = json.load(open(PF)) if os.path.exists(PF) else {'done': 0, 'bad': []}
t0 = time.time()
for k in range(st['done'], len(pairs)):
    i, j = pairs[k]; bi, bj = int(T[i]), int(T[j])
    if any(feasible_pair(bi, oi, bj, oj) for oi in ST[bi] for oj in ST[bj]): st['bad'].append([i, j])
    if k % 20000 == 19999 or k == len(pairs) - 1:
        st['done'] = k + 1; json.dump(st, open(PF + '.tmp', 'w')); os.replace(PF + '.tmp', PF)
        print(k + 1, 'of', len(pairs), 'disagreements', len(st['bad']), round(time.time() - t0), flush=True)
print('DONE checked', len(pairs), 'disagreements', len(st['bad']))
