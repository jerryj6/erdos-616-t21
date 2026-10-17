r"""Wave 12 N-K4 tau-edge CEGAR (driver only; the encoder is w10x_exact/w11_exact unchanged).
Loop: run one w11_exact chunk on the current slot list (k4:3211 base, nk=False: NK is NEVER used).
  UNSAT    -> stop (certificate/controls are done separately with w10x_cert.py etc.).
  REALIZED -> read the literal configuration w10x_TAG_real.json; compute 4-sets B of NAMED points that are transversals of
              the realized family (no realized edge avoids B); add ONE tau-edge 'Jn@B' (an edge avoiding B exists in every
              counterexample by tau>=5, so this is a sound slot; nothing else is assumed about it); restart with a new TAG,
              warm-started from the previous checkpoint (instances are remapped by label; all are instances of proved lemmas).
  timeout  -> same TAG again (checkpoint restore).
Selection of B (heuristic only; soundness does not depend on it): prefer B inside S10 = {v,w} u m3 u alpha u gamma, then
inside the 16-point core; tie-break by a fixed seed.  usage: python3 w12_cegar.py RUN sel=.. [extra=..] [maxrounds=..] [pref=..]
"""
import sys, os, json, itertools, random, subprocess, time
here = os.path.dirname(os.path.abspath(__file__))
sys.path.append(here)
from w10x_exact import setup

def transversal_4sets(names, edges_named, pref):
    nn = len(names); ix = {n: i for i, n in enumerate(names)}
    masks = [sum(1 << ix[a] for a in e if a in ix) for e in edges_named]
    cand = [i for i in range(nn) if names[i][0] in 'Tp']          # core points
    out = []
    pts = list(range(nn))
    # transversals of size <= 4 using core points first (fast), then any named point
    for pool in (cand, pts):
        for B in itertools.combinations(pool, 4):
            bm = sum(1 << b for b in B)
            if all(m & bm for m in masks): out.append(B)
        if out: break
    return out

def min_transversals(edges):
    E = [frozenset(e) for e in edges]; P = sorted(frozenset().union(*E))
    for t in range(1, 4):
        M = [frozenset(S) for S in itertools.combinations(P, t) if all(e & set(S) for e in E)]
        if M: return M
    return []

def score(B, names, pref):
    s10 = set(pref)
    return (sum(names[b] in s10 for b in B), sum(names[b][0] in 'Tp' for b in B))

if __name__ == '__main__':
    RUN = sys.argv[1]
    opt = dict(f.split('=', 1) for f in sys.argv[2:] if '=' in f)
    sel = opt['sel']; extra = opt.get('extra', '')
    pref = opt.get('pref', 'T012_0,T013_0,p01_0,p01_1,p01_2,T023_0,T023_1,T123_0,T123_1,T123_2').split(',')
    maxr = int(opt.get('maxrounds', 12)); rnd = random.Random(int(opt.get('seed', 1)))
    statef = os.path.join(here, f'w12_{RUN}_state.json')
    st = json.load(open(statef)) if os.path.exists(statef) else dict(round=0, extra=extra, tag=f'w12{RUN}r0', prev=None, hist=[])
    while st['round'] < maxr:
        tag = st['tag']
        args = ['./w12_go.sh', 'k4:3211', tag, 'gen1auto=1', f'sel={sel}', 'eager2=1', 'eager3=g1', 'f1all=1', 'tlim=' + opt.get('tlim', '1050'), 'maxadd=600', 'hard=' + opt.get('hard', '1110'), 'phase=1']
        if st['extra']: args.append('extra=' + st['extra'])
        if st['prev'] and not os.path.exists(os.path.join(here, f'w10x_{tag}.json')): args.append('warm=' + f"w10x_{st['prev']}.json")
        if os.path.exists(os.path.join(here, f'w10x_{tag}_real.json')):
            print(time.strftime('%H:%M:%S'), 'reuse existing realization of', tag, flush=True)
        else:
            print(time.strftime('%H:%M:%S'), 'run', tag, st['extra'], flush=True)
            subprocess.run(args, cwd=here)
        log = open(os.path.join(here, f'{tag}.log')).read()
        if os.path.exists(os.path.join(here, f'w10x_{tag}.UNSAT')):
            print('UNSAT at', tag, flush=True); st['result'] = 'UNSAT'; json.dump(st, open(statef, 'w')); break
        realf = os.path.join(here, f'w10x_{tag}_real.json')
        if not os.path.exists(realf):
            print('chunk ended undecided; continuing', flush=True); json.dump(st, open(statef, 'w')); continue
        R = json.load(open(realf)); names = R['names']
        T = transversal_4sets(names, R['edges'], pref)
        if not T:
            print('REALIZED with named tau >= 5: no named 4-set transversal. STOP (needs outside-point tau-edges).', flush=True)
            st['result'] = 'REALIZED_NAMED_TAU5'; json.dump(st, open(statef, 'w')); break
        rnd.shuffle(T); T.sort(key=lambda B: score(B, names, pref), reverse=True)
        if opt.get('mt') == '1':   # W13: prefer B containing the most minimum transversals of the realized family (heuristic only)
            mts = min_transversals(R['edges'])
            red = set(opt.get('avoidB', '').split('|')) - {''}
            T = [B for B in T if '+'.join(sorted(names[b] for b in B)) not in red]
            T.sort(key=lambda B: sum(m <= {names[b] for b in B} for m in mts), reverse=True)
            print('  mt: tau', len(next(iter(mts))) if mts else None, 'min transversals', len(mts), 'best covers', sum(m <= {names[b] for b in T[0]} for m in mts), flush=True)
        B = T[0]; nonext = None
        if opt.get('ext', '1') == '1':
            from w12_ext import Ext
            ex = Ext(R['edges']); t0 = time.time()
            chosen = []
            for Bc in T[:int(opt.get('scanlim', 400))]:
                if ex.extendable(frozenset(names[b] for b in Bc)) is False:
                    chosen.append(Bc); nonext = True
                    if len(chosen) >= int(opt.get('per', 1)): break
            if chosen: B = chosen[0]
            print(f'  ext scan {time.time()-t0:.0f}s nonext={nonext}', flush=True)
        n = st['round'] + 1
        lab = f'J{RUN}{n}'
        tok = f"{lab}@{'+'.join(names[b] for b in B)}"
        if nonext and len(chosen) > 1:
            tok = ';'.join(f"{lab}{chr(97+q)}@{'+'.join(names[b] for b in Bc)}" for q, Bc in enumerate(chosen))
        print(f'  realized; {len(T)} named transversal 4-sets; add {tok}', flush=True)
        st['hist'].append(dict(tag=tag, ntrans=len(T), added=tok, nonext=nonext))
        st['extra'] = (st['extra'] + ';' + tok) if st['extra'] else tok
        st['prev'] = tag; st['round'] = n; st['tag'] = f'w12{RUN}r{n}'
        json.dump(st, open(statef, 'w'))
