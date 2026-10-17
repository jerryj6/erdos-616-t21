r"""Wave 11 Benders on SUB-INSTANCES (a subset of the 24 first-generation singles of the (3,2,1,1)-K4).
UNSAT of a sub-instance implies UNSAT of the 24-slot instance (fewer edges = relaxation).
  python3 w11_sub.py prep TAG i,j,k,...      build master (w8sat '3211', sel = slot list, +TT +SB + eager L4A)
  python3 w11_sub.py run TAG TLIM            Benders chunk
Certificates are stored in w11b_certs/ in FULL slot indexing (0..23 as in w11_meta2.json), so every certificate
is reusable by every instance that contains its slots; the rebuild re-encodes all applicable ones.
Logic identical to w11_benders.run (generic GEN2/GEN3 cuts first, else exact LP scan of subsets of size <= 4)."""
import sys, os, json, glob, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
import w11_benders as WB
from w11_benders import (PEnc, encode_cut, encode_gen, gen_instances, gen_cert, scan, setup, load_cnf, l4a_extra, CERTDIR)
from fractions import Fraction

def log(tag, *a):
    s = ' '.join(str(x) for x in a); print(s, flush=True)
    with open(os.path.join(HERE, f'w11s_{tag}.log'), 'a') as f: f.write(s + '\n')

def prep(tag, sel):
    from w8sat import build
    from pysat.formula import CNF
    t = time.time(); e, X, pts, W = build('3211', sel=sel, tt=True, sb=True, extra=l4a_extra)
    CNF(from_clauses=e.cl).to_file(os.path.join(HERE, f'w11s_{tag}_base.cnf'))
    n = len(pts); P = [[a for a in range(n) if k in pts[a][1]] for k in range(4)]
    full = json.load(open(os.path.join(HERE, 'w11_meta2.json')))['slots']
    slots = []
    for loc, F in enumerate(X):
        fi = sel[loc]; assert full[fi]['pair'] == list(F['pair']) and full[fi]['x'] == pts[F['x']][0]
        slots.append(dict(pair=list(F['pair']), x=pts[F['x']][0], b=F['b'], full=fi))
    meta = dict(names=[p[0] for p in pts], P=P, T=e.T, top=e.pool.top, slots=slots, nclauses=len(e.cl), sel=sel)
    json.dump(meta, open(os.path.join(HERE, f'w11s_{tag}_meta.json'), 'w'))
    print('prep', tag, len(e.cl), e.pool.top, f'{time.time()-t:.0f}s')

def cert_files():
    return sorted(glob.glob(os.path.join(CERTDIR, 'c*.json')), key=lambda p: int(os.path.basename(p)[1:-5]))

def rebuild(meta, bvars, base, f2l):
    enc = PEnc(meta['top'], meta['T']); cuts = []; used = 0
    for p in cert_files():
        rec = json.load(open(p))
        if not all(F in f2l for F in rec['E']): continue
        used += 1
        if rec.get('generic'):
            g = rec['generic']
            cuts.append(encode_gen(enc, (g['kind'], tuple(f2l[x] for x in rec['gen_E']), f2l[g['mid']] if g['mid'] is not None else None, tuple(g['Bp'])), bvars, base))
            continue
        m = lambda F: f2l[F]
        rows = [(k, (tuple(key[0]), tuple(m(x) for x in key[1])) if k == 'L' else tuple(m(x) for x in key), r, Fraction(y)) for k, key, r, y in rec['rows']]
        c = dict(E=[m(F) for F in rec['E']], rows=rows, kap={m(int(F)): Fraction(v) for F, v in rec['kap'].items()})
        bfull = [0] * len(bvars)
        for F, v in rec['traces'].items(): bfull[m(int(F))] = sum(1 << a for a in v)
        cuts.append(encode_cut(enc, c, bfull, bvars, base))
    return enc, enc.cl + cuts, used

def run(tag, tlim, maxk=4):
    from pysat.solvers import Cadical153
    meta = json.load(open(os.path.join(HERE, f'w11s_{tag}_meta.json'))); names, base = setup(meta)
    slots = meta['slots']; n = len(slots); pair = [tuple(s_['pair']) for s_ in slots]; bvars = [s_['b'] for s_ in slots]
    l2f = [s_['full'] for s_ in slots]; f2l = {f: l for l, f in enumerate(l2f)}
    stp = os.path.join(HERE, f'w11s_{tag}_state.json')
    st = json.load(open(stp)) if os.path.exists(stp) else dict(it=0, history=[])
    T0 = time.time()
    cl = load_cnf(os.path.join(HERE, f'w11s_{tag}_base.cnf'))
    enc, cc, used = rebuild(meta, bvars, base, f2l); cl += cc; enc.cl = []
    nextidx = max([int(os.path.basename(p)[1:-5]) for p in cert_files()] + [-1]) + 1
    log(tag, f'== run start it={st["it"]} slots={n} applicable certs={used} clauses={len(cl)} load {time.time()-T0:.0f}s')
    s = Cadical153(bootstrap_with=cl); del cl
    lsp = os.path.join(HERE, f'w11s_{tag}_lastsol.json')   # warm start (added 16:50 EDT): phases = last master solution
    if os.path.exists(lsp):
        ls_ = json.load(open(lsp))
        if ls_.get('full') == l2f:
            s.set_phases([bvars[F][a] if ls_['b'][F] >> a & 1 else -bvars[F][a] for F in range(n) for a in range(61) if bvars[F][a] > 0])
            log(tag, '  phases set from last solution')
    def save(rec):
        nonlocal nextidx
        while os.path.exists(os.path.join(CERTDIR, f'c{nextidx}.json')): nextidx += 1
        rec['idx'] = nextidx; rec['tag'] = tag
        json.dump(rec, open(os.path.join(CERTDIR, f'c{nextidx}.json'), 'w')); nextidx += 1
    while time.time() - T0 < tlim:
        t1 = time.time(); r = s.solve(); ts = time.time() - t1
        if not r:
            log(tag, f'it {st["it"]}: MASTER UNSAT ({ts:.1f}s)'); open(os.path.join(HERE, f'w11s_{tag}.UNSAT'), 'w').write('UNSAT\n'); break
        mdl = set(l for l in s.get_model() if l > 0)
        b = [sum(1 << a for a in range(61) if bvars[F][a] in mdl) for F in range(n)]
        json.dump(dict(b=b, full=l2f), open(os.path.join(HERE, f'w11s_{tag}_lastsol.json'), 'w'))
        tr = lambda F: [a for a in range(61) if b[F] >> a & 1]
        gi = gen_instances(b, base, n, pair); cuts = []
        if gi:
            for inst in gi:
                c = gen_cert(inst); clause = encode_gen(enc, inst, bvars, base); cuts.append(clause)
                kind, E, mid, Bp = inst
                rows = [[k, [list(key[0]), [l2f[x] for x in key[1]]] if k == 'L' else [l2f[x] for x in key], None, str(yv)] for (k, key, r_, yv) in c['rows']]
                save(dict(it=st['it'], E=sorted(l2f[F] for F in c['E']), gen_E=[l2f[x] for x in E],
                          generic=dict(kind=kind, mid=l2f[mid] if mid is not None else None, Bp=list(Bp)),
                          traces={str(l2f[F]): tr(F) for F in c['E']}, pairs={str(l2f[F]): list(pair[F]) for F in c['E']},
                          rows=rows, kap={str(l2f[F]): '1' for F in c['E']}))
            what = f'{len(gi)} GENERIC cuts'
        else:
            t2 = time.time(); newc = list(scan(b, base, pair, maxk, n, budget=max(60, tlim - (time.time() - T0)))); tsc = time.time() - t2
            if not newc:   # fallback (added 16:55 EDT): whole-slot-set LP with lazy L rows + deletion filter (w11_big.py)
                import w11_big as BG
                cand = list(range(n)); t3 = time.time()
                for _ in range(5):
                    c = BG.minimal(cand, b, base, pair, log=lambda *a: log(tag, *a))
                    if not isinstance(c, dict):
                        if c is not None: log(tag, '  big:', c)
                        break
                    newc.append(c); cand = [x for x in cand if x != max(c['E'])]
                tsc += time.time() - t3
                if newc: log(tag, f'  big fallback: {len(newc)} cores, sizes {[len(c["E"]) for c in newc]}')
            if not newc:
                log(tag, f'it {st["it"]}: master SAT ({ts:.1f}s), NO infeasible subset at all (whole-set LP feasible) ({tsc:.0f}s) -> STALL (w11s_{tag}_stall.json)')
                json.dump(dict(b=b, full=l2f, names=names, labels=[f"{p}:{s_['x']}" for p, s_ in zip(pair, slots)]), open(os.path.join(HERE, f'w11s_{tag}_stall.json'), 'w'))
                break
            from w11b_recheck import check as _xcheck
            for c in newc:
                rows = [[k, [list(key[0]), [l2f[x] for x in key[1]]] if k == 'L' else [l2f[x] for x in key], r_, str(yv)] for (k, key, r_, yv) in c['rows']]
                _rec = dict(E=sorted(l2f[F] for F in c['E']), traces={str(l2f[F]): tr(F) for F in c['E']}, pairs={str(l2f[F]): list(pair[F]) for F in c['E']},
                            rows=rows, kap={str(l2f[F]): str(v) for F, v in c['kap'].items()}, gap=str(c['gap']))
                _xcheck(_rec)   # independent exact re-check before the cut is used (raises on failure)
                cuts.append(encode_cut(enc, c, b, bvars, base))
                save(dict(it=st['it'], E=sorted(l2f[F] for F in c['E']), traces={str(l2f[F]): tr(F) for F in c['E']},
                          pairs={str(l2f[F]): list(pair[F]) for F in c['E']}, rows=rows,
                          kap={str(l2f[F]): str(v) for F, v in c['kap'].items()}, gap=str(c['gap'])))
            sz = sorted(len(c['E']) for c in newc); what = f'{len(newc)} LP cuts (|E| {sz[0]}..{sz[-1]}) scan {tsc:.0f}s'
        allc = enc.cl + cuts; enc.cl = []
        with open(os.path.join(HERE, f'w11s_{tag}_cuts.cnf'), 'a') as f:
            for c_ in allc: f.write(' '.join(map(str, c_)) + ' 0\n')
        for c_ in allc: s.add_clause(c_)
        st['history'].append([st['it'], round(ts, 1), what]); log(tag, f'it {st["it"]}: master SAT ({ts:.1f}s); {what}')
        st['it'] += 1; json.dump(st, open(stp, 'w'))
    json.dump(st, open(stp, 'w')); log(tag, f'== run end it={st["it"]} ({time.time()-T0:.0f}s)')

def dump(tag):
    meta = json.load(open(os.path.join(HERE, f'w11s_{tag}_meta.json'))); names, base = setup(meta)
    bvars = [s_['b'] for s_ in meta['slots']]; f2l = {s_['full']: l for l, s_ in enumerate(meta['slots'])}
    enc, cc, used = rebuild(meta, bvars, base, f2l)
    with open(os.path.join(HERE, f'w11s_{tag}_allcuts.cnf'), 'w') as f:
        for c_ in cc: f.write(' '.join(map(str, c_)) + ' 0\n')
    print('dump', tag, 'applicable certs', used, 'clauses', len(cc), 'top', enc.top)

if __name__ == '__main__':
    if sys.argv[1] == 'prep': prep(sys.argv[2], [int(x) for x in sys.argv[3].split(',')])
    elif sys.argv[1] == 'dump': dump(sys.argv[2])
    else: run(sys.argv[2], float(sys.argv[3]))
