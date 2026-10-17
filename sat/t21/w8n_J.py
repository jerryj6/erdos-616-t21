"""w8n_model + extra tau>=5 edges J_B (avoiding 4-set B of model points).  Usage: w8n_J.py CLS WIT B1,B2,... TL
points: M 0-4, A_i = 5+i, C_i = 21+i.  F0: A0={0..3},C0={0..3}; F1 fixed by class."""
import sys, json, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import w8n_model as W
cls = tuple(map(int, sys.argv[1].split(','))); wit = tuple(x for x in sys.argv[2].split(',') if x)
Js = [tuple(map(int, b.split('.'))) for b in sys.argv[3].split(',') if b]
tl = float(sys.argv[4]) if len(sys.argv) > 4 else 80
aa, cc = cls
fixF = {1: (list(range(aa)) + list(range(4, 8 - aa)), list(range(cc)) + list(range(4, 8 - cc)))}
r = W.solve(tl=tl, cls=cls, wit=wit, fam_max=4, fixF=fixF, extraJ=Js)
print(json.dumps({k: v for k, v in r.items() if k != 'sol'}), flush=True)
if 'sol' in r:
    for n, d in r['sol'].items(): print(n, d)
