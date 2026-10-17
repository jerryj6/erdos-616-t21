"""UNSAT core over lazy instances: python3 w9core.py BRANCH TAG -> w9_TAG_core.json (instances in the core)."""
import sys, json, time
from w9cp import *
br, TAG = sys.argv[1], sys.argv[2]
if br.startswith('k4:'): names, B = base_k4(br[3:]); nk = False
else: a, c = map(int, br[5:].split(',')); names, B = base_nok4(a, c); nk = True
st = json.load(open(f'w9_{TAG}.json'))
md = CPM(names, B, nk=nk, acts=True)
for e in st['edges']: md.add_edge(e['avoid'], e['gen'], e['label'])
for ins in st['inst']: md.add_inst(ins)
t0 = time.time(); r = md.solve(tl=1000, workers=1)
print(md.status, f'{time.time()-t0:.0f}s')
if r is None:
    core = [md.inst[i] for i in md.core]
    print('core size', len(core), 'of', len(md.inst))
    json.dump(dict(inst=core), open(f'w9_{TAG}_core.json', 'w'))
