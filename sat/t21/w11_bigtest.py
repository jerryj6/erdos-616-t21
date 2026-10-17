import sys, os, json, time
sys.path.insert(0, '.'); sys.path.insert(0, '../pylib')
import w11_big as BG, w11_benders as WB
from w11b_recheck import check
meta = json.load(open('w11s_A_meta.json')); names, base = WB.setup(meta)
pair = [tuple(s['pair']) for s in meta['slots']]; l2f = [s['full'] for s in meta['slots']]
b = json.load(open(sys.argv[1]))['b']
t = time.time(); c = BG.infeasible(range(len(b)), b, base, pair); print('full E:', 'feasible' if c is None else (c if not isinstance(c, dict) else f"INFEASIBLE |E|={len(c['E'])} gap={c['gap']}"), f'{time.time()-t:.1f}s')
if isinstance(c, dict):
    c = BG.minimal(range(len(b)), b, base, pair)
    rec = dict(E=sorted(l2f[F] for F in c['E']), traces={str(l2f[F]): [a for a in range(61) if b[F] >> a & 1] for F in c['E']},
               pairs={str(l2f[F]): list(pair[F]) for F in c['E']},
               rows=[[k, [list(key[0]), [l2f[x] for x in key[1]]] if k == 'L' else [l2f[x] for x in key], r, str(y)] for k, key, r, y in c['rows']],
               kap={str(l2f[F]): str(v) for F, v in c['kap'].items()}, gap=str(c['gap']))
    print('recheck', check(rec), 'E', rec['E'])
