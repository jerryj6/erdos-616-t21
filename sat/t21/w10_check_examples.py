r"""Wave 10 literal checks on r=16 H(16,10,7) (K=4), r=22 H(22,13,9) (K=5) and the PG(2,4) skeleton (r=21, K=5).
General-r forms (L: empty intersection => union >= 3r-2):
 OO : (X,Y) K-pair, Z&Z'&N = {}  =>  |Z&Z' \ (X u Y)| <= (r+2-K) - |Z&(XuY)| - |Z'&(XuY)|
 HN : OO at the derived pair (X,F), F a single of (X,Y); counted separately for SAME-type singles F',F'' of (X,Y)
 SQ : (X,Y), (X',Y') K-pairs, G = one single per type of (X',Y'), R = X' u Y', W&V&N = {}:
      #{G : W&V&G&(R u X u Y) = {}} <= |W&V \ (R u X u Y)|  (and <= the OO bound)."""
import itertools, random
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
def pg():
    mul = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]; pts = []
    for v in itertools.product(range(4), repeat=3):
        if v == (0,0,0): continue
        f = next(c for c in v if c); inv = [0,1,3,2][f]; w = tuple(mul[inv][c] for c in v)
        if w not in pts: pts.append(w)
    lines = [frozenset(i for i, p in enumerate(pts) if (mul[l[0]][p[0]] ^ mul[l[1]][p[1]] ^ mul[l[2]][p[2]]) == 0) for l in pts]
    C0 = frozenset(range(100, 104)); E = [frozenset(range(21))]
    for i, L in enumerate(lines): E.append(L | C0 | frozenset(range(200 + 12 * i, 212 + 12 * i)))
    return E
for name, E, r, K in [('r=16 H(16,10,7)', H(16, 10, 7), 16, 4), ('r=22 H(22,13,9)', H(22, 13, 9), 22, 5), ('PG(2,4) skeleton', pg(), 21, 5)]:
    random.seed(7)
    kp = [(a, b) for a, b in itertools.combinations(range(len(E)), 2) if len(E[a] & E[b]) == K]
    random.shuffle(kp); kp = kp[:60]
    oo = oov = hn = hnv = sq = sqv = sqpos = 0
    for a, b in kp:
        X, Y = E[a], E[b]; N = X & Y; XY = X | Y
        Es = random.sample(E, min(len(E), 60))
        for Z, Z2 in itertools.combinations(Es, 2):
            if Z & Z2 & N: continue
            oo += 1
            if len((Z & Z2) - XY) > (r + 2 - K) - len(Z & XY) - len(Z2 & XY): oov += 1
        sing = [F for F in E if len(F & N) == 1]
        for F in sing[:6]:
            N2 = X & F
            if len(N2) != K: continue
            XF = X | F
            for F1, F2 in itertools.combinations(sing, 2):
                if (F1 & N) != (F2 & N) or (F1 & N) == (F & N): continue
                if F1 & F2 & N2: continue
                hn += 1
                if len((F1 & F2) - XF) > (r + 2 - K) - len(F1 & XF) - len(F2 & XF): hnv += 1
        for c, d in random.sample(kp, 5):
            X2, Y2 = E[c], E[d]; N2 = X2 & Y2; R = X2 | Y2
            G = {}
            for F in E:
                if len(F & N2) == 1: G.setdefault(next(iter(F & N2)), F)
            for W, V in itertools.combinations(random.sample(E, min(len(E), 40)), 2):
                if W & V & N: continue
                sq += 1; WV = W & V
                cnt = sum(1 for g in G.values() if not (WV & g & (R | XY)))
                if cnt: sqpos += 1
                if cnt > len(WV - (R | XY)): sqv += 1
    print(f'{name}: OO checks={oo} viol={oov}; HN same-type checks={hn} viol={hnv}; SQ checks={sq} (count>0: {sqpos}) viol={sqv}')
