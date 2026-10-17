r"""One-off: symmetric closure of existing certificates whose slots lie in a given instance; images re-checked exactly;
written as JSON lines to w11e_symclose.jsonl (read by w11e_sub.rebuild).  python3 w11e_symclose.py TAG"""
import sys, os, json, glob, time
sys.path.insert(0, '.'); sys.path.insert(0, '../pylib')
import w11e_sym as SY
from w11e_sub import recheck_any
tag = sys.argv[1]; meta = json.load(open(f'w11s_{tag}_meta.json')); sl = {s['full'] for s in meta['slots']}
out = 'w11e_symclose.jsonl'; seen = set()
if os.path.exists(out):
    for line in open(out): seen.add(SY.canon(json.loads(line)))
recs = []
for d in ('w11b_certs', 'w11e_certs'):
    for p in glob.glob(f'{d}/c*.json'):
        r = json.load(open(p))
        if set(r['E']) <= sl: recs.append(r); seen.add(SY.canon(r))
t = time.time(); new = 0
with open(out, 'a') as f:
    for r in recs:
        for g in SY.G:
            im = SY.image(r, g)
            if not set(im['E']) <= sl: continue
            cn = SY.canon(im)
            if cn in seen: continue
            seen.add(cn); recheck_any(im); im['closure'] = tag; f.write(json.dumps(im) + '\n'); new += 1
print(f'{tag}: base certs {len(recs)}, new rechecked images {new} ({time.time()-t:.0f}s)')
