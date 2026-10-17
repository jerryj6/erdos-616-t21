"""Wave 12 (resume): which common transversal 4-sets are NON-extendable (w12_ext) in every given realization. Heuristic only."""
import sys, json, time
from w12_ext import Ext
fs = sys.argv[1:]; C = [tuple(b) for b in json.load(open('/tmp/common.json'))]
exs = [Ext(json.load(open(f))['edges']) for f in fs]
res = {}; t0 = time.time()
for B in C:
    r = []
    for ex in exs:
        v = ex.extendable(frozenset(B), tl=3.0); r.append(v)
        if v is not False: break
    res[B] = r
    if time.time() - t0 > 100: break
good = [B for B, r in res.items() if len(r) == len(exs) and all(v is False for v in r)]
print(len(res), 'tested;', len(good), 'non-extendable in all', flush=True)
json.dump(good, open('w12_commonext.json', 'w'))
for B in good: print(B)
