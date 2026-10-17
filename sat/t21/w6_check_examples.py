"""Literal checks of Wave-6 lemmas on the known examples: r=16 H(16,10,7) (tau=4, window 45, tight analogue)
and r=22 H(22,13,9) (tau=5, window 63, slack analogue).  Checks: min pair = K; D1 analogue (cap 4r-W-3K) at r=16;
uniformity U (all singles of a K-pair have equal A- and C-parts); no triangle (cross-type a=1 never happens)."""
import itertools, random
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
for (r, k, q, K, W) in [(16, 10, 7, 4, 45), (22, 13, 9, 5, 63)]:
    E = H(r, k, q); random.seed(1)
    pairs = [(a, b) for a, b in itertools.combinations(range(len(E)), 2) if len(E[a] & E[b]) == K]
    random.shuffle(pairs); pairs = pairs[:150]
    d1ok = Uok = tri = True; cap = 4 * r - W - 3 * K
    for a, b in pairs:
        X, Y = E[a], E[b]; N = X & Y
        for L in E:
            if L in (X, Y): continue
            if not N <= L and len(L & (X | Y)) > cap: d1ok = False
        sing = [F for F in E if len(F & N) == 1]
        Ap = {frozenset(F & (X - N)) for F in sing}; Cp = {frozenset(F & (Y - N)) for F in sing}
        if len(Ap) != 1 or len(Cp) != 1: Uok = False
        for F, G in itertools.combinations(sing, 2):
            if F & N != G & N and (len(F & G & (X - N)) == 1 or len(F & G & (Y - N)) == 1): tri = False
    print(f'r={r} H({k},{q}) edges={len(E)} K-pairs tested={len(pairs)} D1(cap {cap}) holds={d1ok} '
          f'uniform U holds={Uok} no-triangle={tri}')
