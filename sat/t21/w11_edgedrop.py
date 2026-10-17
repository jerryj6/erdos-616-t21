"""Edge-drop control: python3 w11_edgedrop.py BRANCH TAG LABEL  -> w10x_TAG_no<LABEL>.json (the edge removed from opt
'extra', every instance mentioning it dropped, edge indices re-mapped; K re-derived by setup = KB bound of the smaller set)."""
import sys, os, json
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w10x_exact import setup
from w11_exact import remap
br, T, lab = sys.argv[1:4]
st = json.load(open(f'w10x_{T}.json'))
_, _, _, edges, _, _ = setup(br, st['opt'])
r = [i for i, e in enumerate(edges) if e['label'] == lab]; assert len(r) == 1, r; r = r[0]
o = dict(st['opt']); toks = [t for t in o['extra'].split(';') if t.split('@')[0] != lab]; o['extra'] = ';'.join(toks)
def f(p):
    if p == r: raise KeyError
    return p if p < r else p - 1
inst = []
for ins in st['inst']:
    try: inst.append(remap(ins, f))
    except KeyError: pass
out = dict(st); out['opt'] = o; out['inst'] = inst; out['edgedrop'] = lab
json.dump(out, open(f'w10x_{T}_no{lab}.json', 'w'))
print('dropped', lab, 'kept', len(inst), 'of', len(st['inst']))
