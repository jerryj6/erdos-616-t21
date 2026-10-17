import sys, json, time
sys.path.insert(0, '.'); sys.path.insert(0, '../pylib')
import w11e_oracle as EO, w11_benders as WB
from w11e_recheck import check
from collections import Counter
tag = sys.argv[1]; meta = json.load(open(f'w11s_{tag}_meta.json')); names, base = WB.setup(meta)
pair = [tuple(s['pair']) for s in meta['slots']]; l2f = [s['full'] for s in meta['slots']]
b = json.load(open(sys.argv[2]))['b']; n = len(b)
t = time.time(); cs = list(EO.scan(b, base, pair, 4, n, 100)); print('scan', len(cs), 'certs', f'{time.time()-t:.0f}s')
def mk(k, key):
    f = lambda x: l2f[x]
    if k == 'L': return [list(key[0]), [f(x) for x in key[1]]]
    if k in ('A', 'T', 'L0'): return [f(x) for x in key]
    if k in ('D1B', 'R3P'): return [key[0], f(key[1]), key[2]]
    return [key[0]] + [f(x) for x in key[1:]]
for c in cs[:400]:
    rec = dict(E=sorted(l2f[F] for F in c['E']), traces={str(l2f[F]): [a for a in range(61) if b[F] >> a & 1] for F in c['E']},
               pairs={str(l2f[F]): list(pair[F]) for F in c['E']}, rows=[[k, mk(k, key), r, str(y)] for k, key, r, y in c['rows']],
               kap={str(l2f[F]): str(v) for F, v in c['kap'].items()}, gap=str(c['gap']))
    check(rec)
print('all rechecked; sizes', Counter(len(c['E']) for c in cs), 'kinds', Counter(k for c in cs for k, *_ in c['rows']))
