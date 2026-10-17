r"""Symmetric images of Benders certificates under automorphisms of the (3,2,1,1)-K4 base + its 24 first-generation
singles (full slot indexing of w11_meta2.json).  Generators used: S3 on gamma = T123 (3 points), the swap of the two
alpha = T023 points, and sigma = (P2 P3) (T012<->T013, p02_i<->p03_i, p12<->p13, O2_j<->O3_j).
SOUNDNESS DOES NOT DEPEND ON THIS FILE: every image is a stand-alone certificate (traces, rows, kappa, gap) and is
re-checked exactly by w11e_recheck (rows re-derived at the image traces, slot pair labels from w11_meta2.json) before use."""
import json, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
META = json.load(open(os.path.join(HERE, 'w11_meta2.json')))
NAMES = META['names']; IDX = {nm: i for i, nm in enumerate(NAMES)}
SLOTS = [(tuple(s['pair']), s['x']) for s in META['slots']]; SIDX = {s: i for i, s in enumerate(SLOTS)}

def name_map(gperm, aswap, sig):
    def f(nm):
        if nm.startswith('T123_'): nm = f'T123_{gperm[int(nm[5:])]}'
        if nm.startswith('T023_') and aswap: nm = f'T023_{1 - int(nm[5:])}'
        if sig:
            sw = {'T012_0': 'T013_0', 'T013_0': 'T012_0', 'p12_0': 'p13_0', 'p13_0': 'p12_0'}
            if nm in sw: nm = sw[nm]
            elif nm.startswith('p02_'): nm = 'p03_' + nm[4:]
            elif nm.startswith('p03_'): nm = 'p02_' + nm[4:]
            elif nm.startswith('O2_'): nm = 'O3_' + nm[3:]
            elif nm.startswith('O3_'): nm = 'O2_' + nm[3:]
        return nm
    return f

def group():
    out = []
    for gp in itertools.permutations(range(3)):
        for a in (0, 1):
            for sg in (0, 1):
                if gp == (0, 1, 2) and not a and not sg: continue
                f = name_map(gp, a, sg)
                pt = [IDX[f(nm)] for nm in NAMES]
                bp = [0, 1, 3, 2] if sg else [0, 1, 2, 3]
                sl = []
                for (p, x) in SLOTS:
                    q = tuple(sorted(bp[i] for i in p)); sl.append(SIDX[(q, f(x))])
                out.append((pt, bp, sl))
    return out
G = group()

def image(rec, g):
    pt, bp, sl = g; S = lambda F: sl[int(F)]
    r = dict(rec); r.pop('idx', None)
    r['E'] = sorted(S(F) for F in rec['E'])
    r['traces'] = {str(S(F)): sorted(pt[a] for a in v) for F, v in rec['traces'].items()}
    r['pairs'] = {str(S(F)): list(SLOTS[S(F)][0]) for F in rec['traces']}
    r['kap'] = {str(S(F)): v for F, v in rec['kap'].items()}
    if rec.get('generic'):
        g0 = dict(rec['generic'])
        if g0['kind'].startswith('GD1'): g0.update(k=bp[g0['k']], F=S(g0['F']), L=S(g0['L']))
        else:
            r['gen_E'] = [S(x) for x in rec['gen_E']]; g0['mid'] = S(g0['mid']) if g0['mid'] is not None else None
            g0['Bp'] = sorted(bp[i] for i in g0['Bp'])
        r['generic'] = g0
    rows = []
    for k, key, rr, y in rec['rows']:
        if k == 'L': nk = [sorted(bp[i] for i in key[0]), sorted(S(x) for x in key[1])]
        elif k in ('A', 'T', 'L0'): nk = sorted(S(x) for x in key)
        elif k in ('D1B', 'R3P'): nk = [bp[key[0]], S(key[1]), bp[key[2]]]
        elif k in ('SA', 'W7F', 'W7P'): nk = [bp[key[0]], S(key[1])] + sorted(S(x) for x in key[2:])
        else: nk = [bp[key[0]]] + [S(x) for x in key[1:]]
        rows.append([k, nk, rr, y])
    r['rows'] = rows; r['sym_of'] = rec.get('idx')
    return r

def canon(rec):
    return json.dumps([rec['E'], sorted(rec['traces'].items()), sorted(map(str, rec['rows'])), rec.get('generic')], sort_keys=True)
