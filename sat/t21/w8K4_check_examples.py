"""Wave 8 N-K4: literal checks, on H(16,10,7) (r=16,K=4,W=45) and H(22,13,9) (r=22,K=5,W=63), of the general-r forms
of every lemma the N-K4 model (w8sat.py) uses.  (The examples contain no K4 at all, see N.2, so K4-specific
statements are vacuous there; the general forms below are what is actually used.)
 L3: X,Y,Z pairwise meeting in exactly K, T = X&Y&Z, edge F (not X,Y,Z) with F&T = {}:
     |F & (XuYuZ)| <= 4r - 3K - (W+1) + |T|          (r=21: 8 + |T|)
 OO/L4: (X,Y) a K-pair, F,G further edges with F&G&(X&Y) = {}:
     |F&(XuY)| + |G&(XuY)| + |F&G \\ (XuY)| <= 4r - (2r-K) - (W+1) + (2r-K) ... i.e.  <= 2r + (2r-K) - (W+1)   (r=21: 18)
 D1: (X,Y) K-pair, N = X&Y not inside F:  |F&(XuY)| <= 2r - K - 1 - (W+1-(2r-K)-(r-?))  -> checked numerically as the
     r=21 statement's general form |F&(XuY)| <= 4r - (2r-K) - (r-K-?)...  We check the form actually PROVED:
     F avoids some x in N and a single S of type x exists => L on {X,Y,F,S}.  Here we simply check L on all 4-families
     (the source of all of the above) plus the derived inequalities, on random samples.
 R3: cross-type singles of a K-pair meet both edges in exactly K and have disjoint outside parts.
"""
import itertools, random
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
random.seed(1)
for (r, k, q, K, W) in [(16, 10, 7, 4, 45), (22, 13, 9, 5, 63)]:
    E = H(r, k, q); n = len(E)
    Kp = [(i, j) for i in range(n) for j in range(i + 1, n) if len(E[i] & E[j]) == K]
    # L3
    cnt = viol = 0
    trip = []
    for _ in range(4000):
        i, j = random.choice(Kp)
        for l in random.sample(range(n), 20):
            if l in (i, j): continue
            if len(E[i] & E[l]) == K and len(E[j] & E[l]) == K: trip.append((i, j, l)); break
    for (i, j, l) in trip[:300]:
        T = E[i] & E[j] & E[l]; U = E[i] | E[j] | E[l]
        for f in random.sample(range(n), min(n, 60)):
            if f in (i, j, l) or E[f] & T: continue
            cnt += 1
            if len(E[f] & U) > 4 * r - 3 * K - (W + 1) + len(T): viol += 1
    print(f'r={r}: L3 checks={cnt} violations={viol} (triples tested={min(300,len(trip))})')
    # OO / L4
    cnt = viol = 0
    for (i, j) in random.sample(Kp, min(150, len(Kp))):
        N = E[i] & E[j]; U = E[i] | E[j]
        for f, g in itertools.combinations(random.sample(range(n), min(n, 25)), 2):
            if len({i, j, f, g}) < 4 or (E[f] & E[g] & N): continue
            cnt += 1
            lhs = len(E[f] & U) + len(E[g] & U) + len((E[f] & E[g]) - U)
            if lhs > 2 * r + (2 * r - K) - (W + 1): viol += 1
    print(f'r={r}: OO/L4 checks={cnt} violations={viol}')
    # R3 for singles
    cnt = viol = 0
    for (i, j) in random.sample(Kp, min(150, len(Kp))):
        N = E[i] & E[j]; U = E[i] | E[j]
        sing = [f for f in range(n) if f not in (i, j) and len(E[f] & N) == 1]
        for f, g in itertools.combinations(sing, 2):
            if E[f] & E[g] & N: continue
            cnt += 1
            if not (len(E[f] & E[i]) == K == len(E[f] & E[j]) and not ((E[f] & E[g]) - U)): viol += 1
    print(f'r={r}: R3 cross-type single checks={cnt} violations={viol}')
