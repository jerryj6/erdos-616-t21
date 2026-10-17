"""Permutation groups from small geometries (PG(2,q) q prime, AG(2,3)) acting on points / points+lines."""
import itertools
def pg_q(q):
    pts = []
    for v in itertools.product(range(q), repeat=3):
        if any(v):
            f = next(x for x in v if x); inv = pow(f, -1, q)
            w = tuple((x*inv) % q for x in v)
            if w not in pts: pts.append(w)
    idx = {p: i for i, p in enumerate(pts)}
    def norm(v):
        f = next(x for x in v if x % q); inv = pow(f, -1, q); return tuple((x*inv) % q for x in v)
    lines = [frozenset(idx[p] for p in pts if sum(x*y for x, y in zip(a, p)) % q == 0) for a in pts]
    def mat_pt(M):
        return [idx[norm([sum(M[i][j]*p[j] for j in range(3)) % q for i in range(3)])] for p in pts]
    return pts, lines, mat_pt
MS = lambda q: [[[1,1,0],[0,1,0],[0,0,1]], [[0,0,1],[1,0,0],[0,1,0]], [[2 % q,0,0],[0,1,0],[0,0,1]]]
def gens_pg_pl(q, dual=False):
    pts, lines, mat_pt = pg_q(q); N = len(pts)
    lidx = {l: i for i, l in enumerate(lines)}
    gens = []
    for M in MS(q):
        pp = mat_pt(M)
        lp = [lidx[frozenset(pp[x] for x in l)] for l in lines]
        gens.append(pp + [N + y for y in lp])
    if dual:
        gens.append([N + i for i in range(N)] + list(range(N)))
    return gens, N, lines
def gens_pg_x2(q):
    pts, lines, mat_pt = pg_q(q); N = len(pts)
    gens = [mat_pt(M) + [N + y for y in mat_pt(M)] for M in MS(q)]
    gens.append([N + i for i in range(N)] + list(range(N)))
    return gens
def gens_ag23_pl():
    pts = [(x, y) for x in range(3) for y in range(3)]
    idx = {p: i for i, p in enumerate(pts)}
    lines = set()
    for p in pts:
        for d in [(1,0),(0,1),(1,1),(1,2)]:
            lines.add(frozenset(idx[((p[0]+k*d[0]) % 3, (p[1]+k*d[1]) % 3)] for k in range(3)))
    lines = sorted(lines, key=sorted); lidx = {l: i for i, l in enumerate(lines)}
    maps = [lambda p: ((p[0]+1) % 3, p[1]), lambda p: (p[1], p[0]), lambda p: ((p[0]+p[1]) % 3, p[1]), lambda p: ((2*p[0]) % 3, p[1])]
    gens = []
    for f in maps:
        pp = [idx[f(p)] for p in pts]
        lp = [lidx[frozenset(pp[x] for x in l)] for l in lines]
        gens.append(pp + [9 + y for y in lp])
    return gens
