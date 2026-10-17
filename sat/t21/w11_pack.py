r"""Pack all certificate files (w11b_certs/, w11e_certs/) into w11_pack.jsonl (one line per record, with _pool and _file),
so a chunk loads them with one read instead of thousands of small reads on the slow FS.  Files are kept (source of truth)."""
import os, json, glob
HERE = os.path.dirname(os.path.abspath(__file__)); out = os.path.join(HERE, 'w11_pack.jsonl')
done = set()
if os.path.exists(out):
    for line in open(out): done.add(json.loads(line)['_file'])
n = 0
with open(out, 'a') as f:
    for pool, d in (('b', 'w11b_certs'), ('e', 'w11e_certs')):
        for p in glob.glob(os.path.join(HERE, d, 'c*.json')):
            key = d + '/' + os.path.basename(p)
            if key in done: continue
            r = json.load(open(p)); r['_pool'] = pool; r['_file'] = key; f.write(json.dumps(r) + '\n'); n += 1
print('packed', n, 'new records; total', len(done) + n)
