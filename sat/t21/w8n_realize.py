"""Realize a w8n_model solution as an explicit partial hypergraph and verify it INDEPENDENTLY (plain Python sets):
  * every edge has 21 points; every two edges meet in >= 5;
  * L for EVERY subfamily (all 2^k subsets): union <= 60  =>  common point;
  * NK for EVERY 5-pair (X,Y) inside the family: two singles of different types meet in >= 6;
  * no triangle (implied by NK);  reports the classes (a,c) of all cross-type single pairs of every 5-pair.
Rest points (outside the 97 model points) are realised as fresh points: each pair of var edges gets exactly
ro = max(0, 5 - |model intersection|) private shared fresh points, the remainder of each rest is private.
Usage: python3 w8n_realize.py CLS WIT JLIST TL"""
import sys, os, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import w8n_model as W

def realize(sol):
    E = {'E1': set(W.M + W.A), 'E2': set(W.M + W.C)}
    for n, d in sol.items():
        E[n] = set(d['pts'])
    rest = {n: d['rest'] for n, d in sol.items()}
    nxt = [1000]
    def fresh(k):
        s = set(range(nxt[0], nxt[0] + k)); nxt[0] += k; return s
    var = [n for n in rest if rest[n] > 0]
    left = dict(rest)
    for x, y in itertools.combinations(var, 2):
        need = max(0, 5 - len(E[x] & E[y]))
        if need:
            if left[x] < need or left[y] < need: return None, f'cannot share {need} between {x},{y}'
            s = fresh(need); E[x] |= s; E[y] |= s; left[x] -= need; left[y] -= need
    for n in var: E[n] |= fresh(left[n])
    return E, 'ok'

def verify(E):
    names = list(E); rep = {}
    rep['sizes_ok'] = all(len(E[n]) == 21 for n in names)
    rep['pairs_ok'] = all(len(E[x] & E[y]) >= 5 for x, y in itertools.combinations(names, 2))
    bad = []
    for k in range(2, len(names) + 1):
        for S in itertools.combinations(names, k):
            I = set.intersection(*[E[n] for n in S])
            if I: continue
            U = set.union(*[E[n] for n in S])
            if len(U) <= 60: bad.append((S, len(U)))
    rep['L_violations'] = bad[:5]; rep['L_ok'] = not bad
    nkbad = []; classes = {}
    for X, Y in itertools.combinations(names, 2):
        N = E[X] & E[Y]
        if len(N) != 5: continue
        sing = [Z for Z in names if Z not in (X, Y) and len(E[Z] & N) == 1]
        for Z1, Z2 in itertools.combinations(sing, 2):
            if E[Z1] & E[Z2] & N: continue
            a = len(E[Z1] & E[Z2] & (E[X] - N)); c = len(E[Z1] & E[Z2] & (E[Y] - N))
            classes.setdefault(f'{X}|{Y}', []).append((Z1, Z2, a, c))
            if len(E[Z1] & E[Z2]) < 6: nkbad.append((X, Y, Z1, Z2, len(E[Z1] & E[Z2])))
    rep['NK_violations'] = nkbad[:10]; rep['NK_ok'] = not nkbad
    rep['nonuniform_pairs'] = {k: [t for t in v if (t[2], t[3]) != (4, 4)] for k, v in classes.items()
                               if any((t[2], t[3]) != (4, 4) for t in v)}
    return rep

if __name__ == '__main__':
    cls = tuple(map(int, sys.argv[1].split(','))); wit = tuple(x for x in sys.argv[2].split(',') if x)
    Js = [tuple(map(int, b.split('.'))) for b in sys.argv[3].split(',') if b]
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 100
    aa, cc = cls
    fixF = {1: (list(range(aa)) + list(range(4, 8 - aa)), list(range(cc)) + list(range(4, 8 - cc)))}
    r = W.solve(tl=tl, cls=cls, wit=wit, fam_max=4, fixF=fixF, extraJ=Js)
    print(json.dumps({k: v for k, v in r.items() if k != 'sol'}), flush=True)
    if 'sol' not in r: sys.exit()
    E, msg = realize(r['sol']); print('realize:', msg)
    if E is None: sys.exit()
    rep = verify(E)
    for k, v in rep.items(): print(k, v if k != 'nonuniform_pairs' else {kk: vv[:3] for kk, vv in list(v.items())[:8]})
    json.dump({n: sorted(s) for n, s in E.items()}, open(f'w8n_realized_{aa}{cc}.json', 'w'))
