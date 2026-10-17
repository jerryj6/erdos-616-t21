"""Driver for w9lazy: python3 w9run.py BRANCH TAG [gmax=2] [k=12] [maxit=200] [tlim=1000]
BRANCH: k4:3211 | k4:2221 | nok4:a,c .  Checkpoint: w9_<TAG>.json (edges + lazy instances), rebuilt on restart."""
import sys, json, time, os
from w9lazy import *
br, TAG = sys.argv[1], sys.argv[2]
opt = dict(f.split('=', 1) for f in sys.argv[3:] if '=' in f); flags = [f for f in sys.argv[3:] if '=' not in f]
gmax = int(opt.get('gmax', 2)); K = int(opt.get('k', 12)); maxit = int(opt.get('maxit', 200)); tlim = float(opt.get('tlim', 1000))
if br.startswith('k4:'): names, B = base_k4(br[3:]); nk = False
else: a, c = map(int, br[5:].split(',')); names, B = base_nok4(a, c); nk = True
if 'nonk' in flags: nk = False
md = Model(names, B, nk=nk, gmax=gmax, flags=['clfile=/dev/null']); md.bonly = 'bonly' in flags
ck = f'w9_{TAG}.json'
if os.path.exists(ck):
    st = json.load(open(ck))
    for e in st['edges']: md.add_edge(e['avoid'], e['gen'], e['label'])
    for ins in st['inst']: md.add_inst(ins)
    print('restored', len(md.edges), 'edges', len(md.inst), 'instances', flush=True)
def save():
    json.dump(dict(branch=br, edges=[dict(avoid=e['avoid'], gen=e['gen'], label=e['label']) for e in md.edges], inst=md.inst), open(ck + '.tmp', 'w'))
    os.replace(ck + '.tmp', ck)
T0 = time.time()
nm = lambda S: [names[a] for a in sorted(S)]
for it in range(maxit):
    t0 = time.time(); r = md.solve(); ts = time.time() - t0
    if r is None:
        print(f'it {it}: UNSAT  edges={len(md.edges)} inst={len(md.inst)} clauses={md.ncl} vars={md.top} ({ts:.1f}s)', flush=True)
        save(); open(f'w9_{TAG}.UNSAT', 'w').write('UNSAT\n'); break
    sol, yu = r
    v = find_violations(md, sol, yu)
    pri = {'LA': 0, 'F1t': 1, 'TT': 2, 'NTCg': 3, 'NKg': 4, 'NK': 4, 'L2': 5, 'CAP': 6}
    v.sort(key=lambda x: (pri.get(x[0], 9), len(x[3]) if x[0] == 'L2' else 0))
    added = 0; seenpair = set()
    for x in v:
        if x[0] == 'L2':
            if (x[1], x[2]) in seenpair: continue
            seenpair.add((x[1], x[2]))
        if added >= int(opt.get('maxadd', 250)): break
        added += md.add_inst(x)
    msg = f'it {it}: SAT ({ts:.1f}s) edges={len(md.edges)} inst={len(md.inst)} cl={md.ncl} viol={len(v)} added={added}'
    if added == 0:
        json.dump(dict(branch=br, names=names, base=[sorted(b) for b in B],
                       edges=[dict(label=e['label'], gen=e['gen'], avoid=e['avoid'], pts=sorted(S)) for e, S in zip(md.edges, sol)],
                       yu=[[k[0], k[1], v_] for k, v_ in yu.items() if v_]), open(f'w9_{TAG}_snap.json', 'w'))
        need = needed_edges(md, sol, yu)
        if not need:
            print(msg + ' -> STALL (closed up to gen %d)' % gmax, flush=True); save()
            json.dump(dict(branch=br, names=names, base=[sorted(b) for b in B],
                           edges=[dict(label=e['label'], gen=e['gen'], avoid=e['avoid'], pts=sorted(S)) for e, S in zip(md.edges, sol)],
                           yu=[[k[0], k[1], v_] for k, v_ in yu.items() if v_]), open(f'w9_{TAG}_stall.json', 'w'))
            break
        items = sorted(need.items(), key=lambda kv: (kv[1][0], kv[0]))
        chosen = []
        for key, (g, X_, Y_, y) in items:
            if len(chosen) >= K: break
            chosen.append((key, g, X_, Y_, y))
        for key, g, X_, Y_, y in chosen:
            lab = lambda p: f'B{-1-p}' if p < 0 else f'F{p}'
            md.add_edge(list(key), g, f'g{g}:({lab(X_)},{lab(Y_)}):{names[y]}')
        msg += f' need={len(need)} (gens {sorted(set(v_[0] for v_ in need.values()))}) +edges {len(chosen)}'
    print(msg, flush=True); save()
    if time.time() - T0 > tlim: print('time limit; checkpointed', flush=True); break
