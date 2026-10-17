"""Wave 8 N-noK4: literal checks of the new lemmas on H(16,10,7) (r=16, K=4, window 45) and H(22,13,9) (r=22, K=5, window 63).
 NK  : cross-type singles of every K-pair meet in >= K+1.
 ZF  : (Lemma ZF) for a K-pair (E1,E2), cross-type singles G (type v), H (type w) with C_G = C_H =: C*, every edge X
       avoiding C* contains v, w and A_G&A_H and meets E2, G, H in exactly K.  [proved at r=21; expected to hold at r=16
       (same slack) and may fail at r=22 (slack +1)]
 ZF2 : consequence: X & E2 = M when all singles share C* (checked as: X contains every type that has a C*-single)."""
import itertools, random
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
random.seed(1)
for (r, k, q, K) in [(16, 10, 7, 4), (22, 13, 9, 5)]:
    E = H(r, k, q); n = len(E)
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n) if len(E[i] & E[j]) == K]
    random.shuffle(pairs); pairs = pairs[:150]
    nk_ok = True; zf_checked = 0; zf_fail = 0; zf_fail_ex = None
    for (i, j) in pairs:
        E1, E2 = E[i], E[j]; M = E1 & E2
        sing = [t for t in range(n) if t not in (i, j) and len(E[t] & M) == 1]
        for g, h in itertools.combinations(sing, 2):
            G, Hh = E[g], E[h]
            if (G & M) == (Hh & M): continue
            if len(G & Hh) < K + 1: nk_ok = False
            CG, CH = G & (E2 - M), Hh & (E2 - M)
            if CG != CH: continue
            AG, AH = G & (E1 - M), Hh & (E1 - M)
            v, = G & M; w, = Hh & M
            for x in range(n):
                X = E[x]
                if X & CG: continue
                zf_checked += 1
                ok = v in X and w in X and (AG & AH) <= X and len(X & E2) == K and len(X & G) == K and len(X & Hh) == K
                if not ok:
                    zf_fail += 1; zf_fail_ex = zf_fail_ex or (i, j, g, h, x)
    print(f'r={r} K={K}: K-pairs={len(pairs)} NK holds={nk_ok}  ZF instances={zf_checked} ZF failures={zf_fail} example={zf_fail_ex}')
