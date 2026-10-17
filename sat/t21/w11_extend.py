"""Wave 11: choose new tau-edges from a violation-free realization (W9-style generation step).
python3 w11_extend.py REAL.json BRANCH [k=6] [prev=EXTRA_STRING]
For every 5-pair (X,Y) of the realization whose intersection N consists of NAMED points, every type y in N that has no
single among the realized edges gives the candidate 'an edge avoiding N\\{y}' (sound for ANY 4-set by tau >= 5; in a real
configuration that agrees with the realization on X,Y it is the missing type-y single, by R.1).  Priority: pairs
(B_i, F) with F a model edge (second generation) before pairs of two new edges; base pairs never occur (all types
of base pairs are present).  Prints the new 'extra' option string (previous extras + up to k new ones, distinct pairs
first)."""
import sys, json, itertools, os
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w9lazy import base_nok4
d = json.load(open(sys.argv[1])); br = sys.argv[2]
opt = dict(f.split('=', 1) for f in sys.argv[3:] if '=' in f)
k = int(opt.get('k', 6)); prev = opt.get('prev', '')
a, c = map(int, br[5:].split(',')); names, B = base_nok4(a, c); named = set(names)
E = [frozenset(x) for x in d['edges']]; lab = d['labels']; n = len(E)
have = set()
for t in prev.split(';'):
    if t: have.add(frozenset(t.split('@')[1].split('+')))
# avoid sets of existing model edges (gen-1 singles avoid N\{y} at base pairs; reconstruct from labels is unnecessary:
# a candidate equal to an existing edge's avoid set is detected because that edge is then a single of the pair)
cand = []
for i, j in itertools.combinations(range(n), 2):
    N = E[i] & E[j]
    if len(N) != 5 or not N <= named: continue
    nbase = (i < 4) + (j < 4)
    if nbase == 2: continue
    types = set()
    for z in range(n):
        if z in (i, j): continue
        t = E[z] & N
        if len(t) == 1: types |= t
    for y in sorted(N - types):
        av = frozenset(N - {y})
        if av in have: continue
        cand.append((-nbase, lab[i], lab[j], y, av))
cand.sort(key=lambda t: (t[0], t[1], t[2], t[3]))
print('# candidates', len(cand), 'gen2-pairs', sum(1 for t in cand if t[0] == -1), file=sys.stderr)
out = [t for t in prev.split(';') if t]; usedpairs = set(); picked = 0
for rnd in (0, 1):
    for t in cand:
        if picked >= k: break
        av = t[4]
        if av in have: continue
        if rnd == 0 and (t[1], t[2]) in usedpairs: continue
        tag = f"g2[{t[1].replace('g1:','').replace(':','.')}|{t[2].replace('g1:','').replace(':','.')}].{t[3]}".replace(';', ',').replace('@', 'at')
        out.append(tag + '@' + '+'.join(sorted(av, key=names.index)))
        have.add(av); usedpairs.add((t[1], t[2])); picked += 1
        print('#', tag, sorted(av), file=sys.stderr)
print(';'.join(out))
