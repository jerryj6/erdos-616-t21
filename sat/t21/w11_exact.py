r"""Wave 11: lean driver around w10x_exact.Exact (same encoder, same clause semantics, same checkpoint format).
Checkpoint: w10x_TAG.json (so w10x_core.py / w10x_cert.py / w10x_verify.py work unchanged; setup() rebuilds the edge
list from opt incl. 'sel').  Every eager instance is added through add_inst, so it is stored in the checkpoint and
rebuilt by the core/cert scripts.

Extra eager layers (all are INSTANCES of the same proved lemmas as in w10x; nothing new is assumed):
  eager3=1 : W7(+NK) and SA for every pair of edges (z1,z2) at every SECOND-generation 5-pair (B_X, F), F a single of a
             base pair through B_X (a 5-pair by R.3, itself encoded).  [The (2,4) core used 35 W7 + 62 SA at such pairs.]
  f1all=1  : L on every triple of new edges (= F1: every three edges share a point).
  l4b=1    : L (counter form) on every 4-family {B_k, F, G, H} with one base edge and three new edges (= Lemma SF).
  warm=CK  : restore the instances of another checkpoint CK whose edges all occur here (mapped by label).
usage: python3 w11_exact.py BRANCH TAG gen1auto=1 sel=.. eager2=1 eager3=1 f1all=1 [l4b=1] [warm=..] tlim=.. maxadd=..
"""
import sys, os, json, time, itertools
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w10x_exact import Exact, setup, check, literal

def eidx(z, nb): return -1 - z if z < 0 else nb + z   # position in check()'s E list

def eager3(md, g1only=False, n24=True):
    nb = md.nb; allE = list(range(-nb, 0)) + [q for q in range(len(md.edges)) if not g1only or md.edges[q]['groups']]; cnt = 0
    for p, e in enumerate(md.edges):
        for (i, j, y) in e['groups']:
            for X in (i, j):
                bx = -1 - X
                others = sorted([z for z in allE if z not in (p, bx)], key=lambda z: eidx(z, nb))
                for z1, z2 in itertools.combinations(others, 2):
                    cnt += md.add_inst(['W7', bx, p, z1, z2]) + md.add_inst(['SA', bx, p, z1, z2])
                    if n24 and getattr(md, 'no24', False): cnt += md.add_inst(['N24', bx, p, z1, z2])
    return cnt

def remap(ins, f):
    k = ins[0].lstrip('X')
    if k == 'L': return [ins[0], [f(p) for p in ins[1]]]
    if k == 'TT': return [ins[0], f(ins[1]), [f(p) for p in ins[2]]]
    return [ins[0]] + [f(p) for p in ins[1:]]

if __name__ == '__main__':
    br, TAG = sys.argv[1], sys.argv[2]
    opt = dict(f.split('=', 1) for f in sys.argv[3:] if '=' in f)
    here = os.path.dirname(os.path.abspath(__file__))
    names, B, nk, edges, K, Kb = setup(br, opt)
    tlim = float(opt.get('tlim', 1000)); maxadd = int(opt.get('maxadd', 400))
    print(f'[w11] branch {br} edges {len(edges)} K={K} (KB bound {Kb}; sound={K >= Kb}) opt={opt}', flush=True)
    print('  edges:', [e['label'] for e in edges], flush=True)
    t0 = time.time()
    md = Exact(names, B, edges, K, nk)
    md.no24 = bool(opt.get('no24'))   # use the Wave-10 (2,4) theorem: no 5-pair has cross-type singles of class (2,4)/(4,2)
    ck = os.path.join(here, f'w10x_{TAG}.json')
    if os.path.exists(ck):
        st = json.load(open(ck))
        for ins in st['inst']: md.add_inst(ins)
        print('restored', len(md.inst), 'instances', flush=True)
    else:
        if opt.get('eager2'): print('eager2', md.eager2(), flush=True)
        if opt.get('eager3'): print('eager3', eager3(md, g1only=(opt['eager3'] == 'g1'), n24=(opt.get('n24g2', '1') == '1')), flush=True)
        if md.no24:
            c = 0; allE = list(range(-md.nb, 0)) + list(range(len(md.edges)))
            for (i, j) in md.bpairs:
                oth = sorted([z for z in allE if z not in (-1 - i, -1 - j)], key=lambda z: eidx(z, md.nb))
                for z1, z2 in itertools.combinations(oth, 2):
                    if z1 < 0 and z2 < 0: continue
                    c += md.add_inst(['N24', -1 - i, -1 - j, z1, z2])
            print('no24 base-pair instances', c, flush=True)
        if opt.get('f1all'):
            c = 0
            for t in itertools.combinations(range(len(md.edges)), 3): c += md.add_inst(['L', list(t)])
            print('f1all', c, flush=True)
        if opt.get('l4b'):
            c = 0
            for k in range(md.nb):
                for t in itertools.combinations(range(len(md.edges)), 3):
                    c += md.add_inst(['L', [-1 - k] + list(t)])
            print('l4b', c, flush=True)
        if opt.get('warm'):
            w = json.load(open(os.path.join(here, opt['warm'])))
            _, _, _, wedges, _, _ = setup(br, w.get('opt', {}))
            lab = {e['label']: i for i, e in enumerate(edges)}
            mp = {i: lab.get(e['label']) for i, e in enumerate(wedges)}
            c = 0
            for ins in w['inst']:
                try: r = remap(ins, lambda p: p if p < 0 else (mp[p] if mp[p] is not None else (_ for _ in ()).throw(KeyError)))
                except KeyError: continue
                c += md.add_inst(r)
            print('warm', c, flush=True)
    print(f'built {time.time()-t0:.1f}s vars={md.top} clauses={md.ncl} inst={len(md.inst)} tags={md.tags}', flush=True)
    def save(extra=None):
        d = dict(branch=br, K=K, Kb=Kb, opt={k: v for k, v in opt.items() if k in ('gen1auto', 'sel', 'nedges', 'src', 'K', 'extra')}, inst=md.inst, driver='w11_exact.py')
        if extra: d.update(extra)
        json.dump(d, open(ck + '.tmp', 'w')); os.replace(ck + '.tmp', ck)
    save()
    phf = os.path.join(here, f'w10x_{TAG}_phase.npy')   # W12 resume: solver phase hint only (no clause changes)
    if opt.get('phase') and os.path.exists(phf):
        import numpy as _np; _ph = [int(l) for l in _np.load(phf) if abs(int(l)) <= md.top]; md.solver.set_phases(_ph); print('phases set', len(_ph), flush=True)
    T0 = time.time()
    for it in range(100000):
        t1 = time.time(); r = md.solve(); ts = time.time() - t1
        if r is None:
            print(f'it {it}: UNSAT ({ts:.1f}s) inst={len(md.inst)} vars={md.top} clauses={md.ncl} sound={K >= Kb}', flush=True)
            save(dict(result='UNSAT')); open(os.path.join(here, f'w10x_{TAG}.UNSAT'), 'w').write('UNSAT\n'); break
        if opt.get('phase'):
            import numpy as _np; _np.save(phf + '.tmp.npy', _np.array(md.solver.get_model(), dtype=_np.int32)); os.replace(phf + '.tmp.npy', phf)
        v = check(md, r)
        pri = {'A?': 0, 'R3': 1, 'SA': 1, 'W7': 2, 'N24': 2, 'TT': 2, 'D1': 3, 'L': 4}
        v.sort(key=lambda z: (pri[z[0]], len(z[1]) if z[0] == 'L' else 0))
        assert not any(z[0] == 'A?' for z in v)
        byk = {}
        for z in v: byk.setdefault(z[0], []).append(z)
        rr = []; its = [iter(l) for l in byk.values()]
        while its:
            nxt = []
            for itr in its:
                z = next(itr, None)
                if z is not None: rr.append(z); nxt.append(itr)
            its = nxt
        v = rr; added = 0; esc = 0
        for z in v:
            if added >= maxadd: break
            if json.dumps(z) in md.instset and z[0] == 'N24': print('BUG: N24 present but violated', z, flush=True); continue
            if json.dumps(z) in md.instset:
                z = ['X' + z[0]] + z[1:]; esc += 1
                if json.dumps(z) in md.instset: print('BUG: exact instance present but violated', z, flush=True); continue
            added += md.add_inst(z)
        kinds = {}
        for z in v: kinds[z[0]] = kinds.get(z[0], 0) + 1
        pu = sorted(set(a for S in r for a in S if a >= md.nn))
        print(f'it {it}: SAT ({ts:.1f}s) inst={len(md.inst)} cl={md.ncl} viol={len(v)} {kinds} added={added} esc={esc} pool_used={len(pu)}', flush=True)
        if added == 0:
            if v: print('WARNING: violations not encodable/duplicate', v[:5], flush=True)
            E = literal(md, r)
            json.dump(dict(branch=br, names=md.names, labels=[f'B{i}' for i in range(md.nb)] + [e['label'] for e in md.edges],
                           edges=[sorted(str(a) if isinstance(a, tuple) else md.names[a] for a in X) for X in E]),
                      open(os.path.join(here, f'w10x_{TAG}_real.json'), 'w'))
            print('VIOLATION-FREE: literal configuration written', flush=True); save(dict(result='REALIZED')); break
        save()
        if time.time() - T0 > tlim: print('time limit; checkpointed', flush=True); break
        if 'hard' in opt and time.time() - T0 + 1.15 * ts > float(opt['hard']): print('next solve would pass hard limit; checkpointed', flush=True); break  # W12 resume: driver-only
