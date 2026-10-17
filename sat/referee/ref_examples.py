"""Referee literal checks on EHT examples H(16,10,7) and H(22,13,9) (core n, edges = k-subsets of core + r-k privates),
plus the PG(2,4) skeleton of §7.2. Checks general-r analogues of Lemma A, R.1-R.3, S(a)(b)(c), T, K, D1, CP'."""
import itertools as it, random
random.seed(1)
def build(r, n, k):
    E = []; nxt = n
    for s in it.combinations(range(n), k):
        E.append(frozenset(s) | frozenset(range(nxt, nxt + r - k))); nxt += r - k
    return E
def check(r, n, k, npairs=60):
    E = build(r, n, k); m = len(E)
    K = min(len(E[i] & E[j]) for i in range(m) for j in range(i+1, m))
    tau_lb = n - k + 1  # core cover size needed
    pairs = [(i, j) for i in range(m) for j in range(i+1, m) if len(E[i] & E[j]) == K]
    random.shuffle(pairs); bad = {}
    def flag(name, ok):
        bad.setdefault(name, 0)
        if not ok: bad[name] += 1
    D1cap = r - 3*K + 3
    for (i, j) in pairs[:npairs]:
        e1, e2 = E[i], E[j]; M = e1 & e2; U = e1 | e2
        flag('R1 M transversal', all(F & M for F in E))
        sing = {x: [F for F in E if F & M == {x}] for x in M}
        flag('R2 singles of every type', all(sing[x] for x in M))
        A, C = e1 - M, e2 - M
        for x in M:
            for F in sing[x]:
                flag('R3 |F&E|=|F&E\'|=K', len(F & e1) == K and len(F & e2) == K)
        for x, y in it.permutations(M, 2):
            for G in sing[x][:6]:
                for H in sing[y][:6]:
                    AG, AH, CG, CH = G & A, H & A, G & C, H & C
                    flag('S(a)', bool(AG & AH) and bool(CG & CH) and not ((G - U) & (H - U)))
                    flag('S(b)', len(AG & AH) + len(CG & CH) >= K)
                    if len(AG & AH) == 1: flag('S(c)', CG == CH)
                    flag('uniform', AG == AH and CG == CH)
        for L in E:
            if not M <= L: flag('D1 cap', len(L & U) <= D1cap)
        # Lemma K (multi edges): |K&A|,|K&C| >= K-k
        for Kd in E:
            kq = len(Kd & M)
            if kq >= 2 and Kd not in (e1, e2):
                flag('K first line', len(Kd & A) >= K - kq and len(Kd & C) >= K - kq)
    print(f'r={r} H({n},{k}) edges={m} minpair={K} D1cap={D1cap} pairs={min(npairs,len(pairs))}',
          {a: ('ok' if b == 0 else f'FAIL x{b}') for a, b in bad.items()})
check(16, 10, 7); check(22, 13, 9)
# PG(2,4) skeleton (§7.2): verify L at r=21 literally (all minimal empty-intersection subfamilies) and CP'
F4 = [(a, b) for a in range(2) for b in range(2)]
def mul(x, y):  # GF(4) as F2[w]/(w^2+w+1)
    a, b = x; c, d = y
    return ((a*c + b*d) % 2, (a*d + b*c + b*d) % 2)
def add(x, y): return ((x[0]+y[0]) % 2, (x[1]+y[1]) % 2)
els = F4
vecs = [v for v in it.product(els, repeat=3) if v != ((0,0),)*3]
def norm(v):
    for c in v:
        if c != (0,0):
            inv = [e for e in els if mul(c, e) == (1,0)][0]; return tuple(mul(inv, t) for t in v)
pts = sorted(set(norm(v) for v in vecs)); assert len(pts) == 21
def dot(u, v):
    s = (0,0)
    for a, b in zip(u, v): s = add(s, mul(a, b))
    return s
lines = [frozenset(i for i, p in enumerate(pts) if dot(p, l) == (0,0)) for l in pts]
assert all(len(l) == 5 for l in lines)
C0 = frozenset(range(21, 25)); nxt = 25; edges = [frozenset(range(21))]
for l in lines: edges.append(l | C0 | frozenset(range(nxt, nxt+12))); nxt += 12
assert all(len(e) == 21 for e in edges)
# L: minimal empty-intersection families need Q + >=3 non-concurrent lines; check all 3-line and 4-line subfamilies with Q
viol = 0
for t in (3, 4):
    for S in it.combinations(range(1, 22), t):
        fam = [edges[0]] + [edges[s] for s in S]
        if not frozenset.intersection(*fam) and len(frozenset.union(*fam)) <= 60: viol += 1
cpv = 0; cpn = 0
for a, b, c in it.combinations(range(22), 3):
    X = [edges[a], edges[b], edges[c]]
    if all(len(X[u] & X[v]) == 5 for u, v in it.combinations(range(3), 2)):
        T = X[0] & X[1] & X[2]
        if len(T) == 1:
            p = next(iter(T))
            for Q_, X1, X2 in [(X[0], X[1], X[2]), (X[1], X[0], X[2]), (X[2], X[0], X[1])]:
                for F in edges:
                    if p in F: continue
                    cpn += 1
                    if len((F & Q_) - (X1 | X2)) > len(F & ((X1 & X2) - Q_)) - 1: cpv += 1
print(f'PG(2,4) skeleton: L violations among Q+3/4 lines = {viol}; CP\' checks = {cpn}, violations = {cpv}')
