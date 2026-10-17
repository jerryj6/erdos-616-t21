# PΓL(3,4) acting on the 21 points of PG(2,4)
import itertools
# GF(4) = {0,1,2,3} with 2=w, 3=w^2=w+1
ADD = [[a ^ b for b in range(4)] for a in range(4)]
EXP = [1, 2, 3]; LOG = {1: 0, 2: 1, 3: 2}
def mul(a, b):
    if a == 0 or b == 0: return 0
    return EXP[(LOG[a] + LOG[b]) % 3]
def norm(v):
    for x in v:
        if x:
            inv = EXP[(-LOG[x]) % 3]
            return tuple(mul(inv, y) for y in v)
pts = sorted({norm(v) for v in itertools.product(range(4), repeat=3) if any(v)})
idx = {p: i for i, p in enumerate(pts)}
def matperm(M):
    out = []
    for p in pts:
        w = [0, 0, 0]
        for i in range(3):
            s = 0
            for j in range(3):
                s ^= mul(M[i][j], p[j])
            w[i] = s
        out.append(idx[norm(w)])
    return out
frob = [idx[norm(tuple(mul(x, x) for x in p))] for p in pts]
gens = [matperm([[1,1,0],[0,1,0],[0,0,1]]), matperm([[0,0,1],[1,0,0],[0,1,0]]), matperm([[2,0,0],[0,1,0],[0,0,1]]),
        matperm([[1,0,0],[0,1,1],[0,0,1]]), frob]
lines = sorted({frozenset(idx[p] for p in pts if (mul(a[0],p[0]) ^ mul(a[1],p[1]) ^ mul(a[2],p[2])) == 0) for a in pts}, key=sorted)
