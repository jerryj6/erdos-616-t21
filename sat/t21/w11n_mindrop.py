"""Wave 11 noK4: drop several extra tau-edges at once (generalises w11_edgedrop.py).
python3 w11n_mindrop.py BRANCH SRC_TAG OUT_TAG 'LAB1;LAB2;..'  -> w10x_OUT_TAG.json
Instances mentioning a dropped edge are removed; indices remapped; K re-derived by setup (KB bound of the smaller set)."""
import sys, os, json
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w10x_exact import setup
from w11_exact import remap
br, T, OUT, labs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4].split(';')
st = json.load(open(f'w10x_{T}.json'))
_, _, _, edges, _, _ = setup(br, st['opt'])
rm = sorted(i for i, e in enumerate(edges) if e['label'] in labs); assert len(rm) == len(labs), (rm, labs)
o = dict(st['opt']); o['extra'] = ';'.join(t for t in o['extra'].split(';') if t.split('@')[0] not in labs)
def f(p):
    if p in rm: raise KeyError
    return p if p < 0 else p - sum(1 for r in rm if r < p)
inst = []
for ins in st['inst']:
    try: inst.append(remap(ins, f))
    except KeyError: pass
out = dict(st); out['opt'] = o; out['inst'] = inst; out['edgedrop'] = labs; out['src'] = T
json.dump(out, open(f'w10x_{OUT}.json', 'w'))
_, _, _, e2, K, Kb = setup(br, o)
print('dropped', labs, 'kept', len(inst), 'of', len(st['inst']), 'edges', len(e2), 'K', K, [e['label'] for e in e2 if e['gen'] == 2])
