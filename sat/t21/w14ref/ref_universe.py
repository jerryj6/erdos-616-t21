"""REFEREE: merge my state chunks; compare with the authors' variable universe (w14_conf.npz 'T' = CNF var-1 -> trace,
w13_feas.json, w14_states.json) as DATA only; write ref_states.npz (var, b, o) with var = authors' CNF variable."""
import json, glob, numpy as np
from ref_states import Pm, PR, pc
res = {}
for f in glob.glob('ref_states_*_*.json'):
    lo, hi = map(int, f[11:-5].split('_'))
    d = json.load(open(f))
    for k, v in d.items():
        assert lo <= int(k) < hi
        res[int(k)] = [tuple(x) for x in v]
covered = set()
for f in glob.glob('ref_states_*_*.json'):
    lo, hi = map(int, f[11:-5].split('_')); covered |= set(range(lo, hi))
assert covered == set(range(65536)), ('missing chunks', 65536 - len(covered))
mine = sorted(res); nst = sum(len(v) for v in res.values())
print('my feasible traces', len(mine), 'my states', nst)
T = np.load('../w14/w14_conf.npz')['T'].tolist()
feas = json.load(open('../w13_feas.json'))
print('authors T == sorted(w13_feas):', T == sorted(feas), 'len', len(T))
print('mine - theirs', len(set(mine) - set(T)), 'theirs - mine', len(set(T) - set(mine)))
ST = {b: set(map(tuple, s)) for b, s in json.load(open('../w14/w14_states.json'))}
dif = sum(1 for b in mine if set(res[b]) != ST.get(b, set())) + sum(1 for b in ST if b not in res)
print('state sets differing (trace count):', dif, ' authors states', sum(len(s) for s in ST.values()))
lut = {t: i + 1 for i, t in enumerate(T)}
var = []; B = []; O = []
for b in mine:
    if b not in lut: continue
    for o in res[b]: var.append(lut[b]); B.append(b); O.append(o)
o = np.argsort(np.array(var), kind='stable')
np.savez('ref_states.npz', var=np.array(var)[o], b=np.array(B, np.int64)[o], o=np.array(O, np.int64)[o])
json.dump({'traces': mine}, open('ref_feas.json', 'w'))
