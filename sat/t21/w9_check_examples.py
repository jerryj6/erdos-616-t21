"""Wave 9 literal checks of Lemma U1 (avoiders of a uniform pair's common A-part) and Lemma OD on the known examples
r=16 H(16,10,7) (K=4) and r=22 H(22,13,9) (K=5).  U1 (general-K form): for a uniform K-pair (X,Y) with parts A0,C0
and S = N u A0 u C0, every edge Z with Z∩A0 = ∅ has Z∩S = N u C0, Z∩X = N and Z∩O_z = ∅ for every single's outside."""
import itertools, random
def H(r, k, q):
    E = []; nxt = k
    for Y in itertools.combinations(range(k), q):
        E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
    return E
for (r, k, q, K) in [(16, 10, 7, 4), (22, 13, 9, 5)]:
    E = H(r, k, q); random.seed(2)
    pairs = [(a, b) for a, b in itertools.combinations(range(len(E)), 2) if len(E[a] & E[b]) == K]
    random.shuffle(pairs); pairs = pairs[:150]
    nU = 0; bad = 0; nZ = 0; od_hyp = 0
    for a, b in pairs:
        X, Y = E[a], E[b]; N = X & Y
        sing = [F for F in E if len(F & N) == 1]
        Ap = {frozenset(F & (X - N)) for F in sing}; Cp = {frozenset(F & (Y - N)) for F in sing}
        if len(Ap) != 1 or len(Cp) != 1: continue
        nU += 1; A0, = Ap; C0, = Cp; S = N | A0 | C0
        outs = [F - (X | Y) for F in sing]
        for Z in E:
            if Z & A0: continue
            nZ += 1
            if Z & S != N | C0 or Z & X != N or any(Z & o for o in outs): bad += 1
        # OD hypothesis: all types but one share parts and a deviant exists -> never in uniform pairs
    print(f'r={r}: uniform K-pairs={nU}/{len(pairs)}, A0-avoiders checked={nZ}, U1 violations={bad}')
# P-red (b)/(c) literal: for a uniform K-pair, single F_y and p in A0, every edge avoiding {y} ∪ (A0\p) has (k,c) = (K-1, |C0|)
for (r, k, q, K) in [(16, 10, 7, 4), (22, 13, 9, 5)]:
    E = H(r, k, q); random.seed(3)
    pairs = [(a, b) for a, b in itertools.combinations(range(len(E)), 2) if len(E[a] & E[b]) == K]
    random.shuffle(pairs); pairs = pairs[:40]; nW = bad = 0
    for a, b in pairs:
        X, Y = E[a], E[b]; N = X & Y
        sing = [F for F in E if len(F & N) == 1]
        A0 = frozenset(sing[0] & (X - N)); C0 = frozenset(sing[0] & (Y - N))
        for y in N:
            for p in A0:
                D = {y} | (A0 - {p})
                for W in E:
                    if W & D: continue
                    nW += 1
                    if len(W & N) != K - 1 or W & C0 != C0 or (W & (X - N)) != {p}: bad += 1
    print(f'r={r}: (X,F_y) type-p singles checked={nW}, deviant (k,c)!=(K-1,|C0|): {bad}')
