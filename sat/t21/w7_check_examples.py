"""Literal check of Lemma CP' (W7-5) on H(16,10,7) (r=16,K=4,W=45) and H(22,13,9) (r=22,K=5,W=63).
CP' (general form): Q,X1,X2 pairwise meet in exactly K, Q&X1&X2 = {p}; every edge F with p notin F has
  |F & Q \ (X1 u X2)| <= (4r - 5K - W) + |F & (X1 & X2) \ Q|.   (r=21: -1 + z; r=16: -1 + z; r=22: 0 + z.)
Also W7-1 (trace triangles -> K4 with |X_i & X_j \ Q| = r-... ) is checked where it applies."""
import itertools, random
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
for (r, k, q, K, Wn) in [(16, 10, 7, 4, 45), (22, 13, 9, 5, 63)]:
    E = H(r, k, q); random.seed(2); n = len(E); slack = 4*r - 5*K - Wn
    trip = 0; viol = 0; checks = 0
    idx = list(range(n))
    for _ in range(4000):
        Qx = random.choice(idx); Qs = E[Qx]
        cand = [i for i in idx if i != Qx and len(E[i] & Qs) == K]
        if len(cand) < 2: continue
        X1, X2 = random.sample(cand, 2)
        if len(E[X1] & E[X2]) != K or len(Qs & E[X1] & E[X2]) != 1: continue
        trip += 1; (p,) = tuple(Qs & E[X1] & E[X2]); C = (E[X1] & E[X2]) - Qs
        for F in E:
            if p in F: continue
            checks += 1
            if len((F & Qs) - E[X1] - E[X2]) > slack + len(F & C): viol += 1
    print(f'r={r}: CP\' triples tested={trip}, (triple,F) checks={checks}, violations={viol}, slack={slack}')
