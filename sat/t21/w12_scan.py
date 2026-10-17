"""Scan named transversal 4-sets of a realized family for NON-extendable ones (w12_ext). usage: w12_scan.py real.json [limit] [out]"""
import sys, json, time
from w12_ext import Ext
from w12_cegar import transversal_4sets, score
R = json.load(open(sys.argv[1])); names = R['names']; lim = int(sys.argv[2]) if len(sys.argv) > 2 else 10**9
pref = 'T012_0,T013_0,p01_0,p01_1,p01_2,T023_0,T023_1,T123_0,T123_1,T123_2'.split(',')
T = transversal_4sets(names, R['edges'], pref); T.sort(key=lambda B: score(B, names, pref), reverse=True)
ex = Ext(R['edges']); t0 = time.time(); res = []
for B in T[:lim]:
    nb = [names[b] for b in B]; r = ex.extendable(frozenset(nb))
    res.append((nb, r))
    if r is not True: print(nb, r, flush=True)
print(f'{len(res)} tested in {time.time()-t0:.0f}s; non-extendable {sum(r is False for _,r in res)}; unknown {sum(r is None for _,r in res)}', flush=True)
if len(sys.argv) > 3: json.dump(res, open(sys.argv[3], 'w'))
