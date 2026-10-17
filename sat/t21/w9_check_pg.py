"""Wave 9: PG(2,4) skeleton (7.2): Q = 21 points, X_l = l ∪ C0 ∪ O_l.  Count 5-pairs, uniform 5-pairs (hypothesis of U1)
and 'one-deviant' 5-pairs (hypothesis of OD: >=2 types with a common single part (A0,C0), and a type w whose singles deviate)."""
import itertools
# GF(4) = {0,1,a,a^2} as 0..3 with a^2 = a+1
add = lambda x, y: x ^ y
mul_t = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
pts = []
for v in itertools.product(range(4), repeat=3):
    if v == (0,0,0): continue
    f = next(c for c in v if c); inv = [0,1,3,2][f]
    w = tuple(mul_t[inv][c] for c in v)
    if w not in pts: pts.append(w)
lines = []
for l in pts:
    L = frozenset(i for i, p in enumerate(pts) if (mul_t[l[0]][p[0]] ^ mul_t[l[1]][p[1]] ^ mul_t[l[2]][p[2]]) == 0)
    lines.append(L)
assert len(pts) == 21 and all(len(L) == 5 for L in lines)
C0 = frozenset(range(100, 104)); E = [frozenset(range(21))]
for i, L in enumerate(lines): E.append(L | C0 | frozenset(range(200 + 12 * i, 212 + 12 * i)))
npair = nuni = nod = 0
for a, b in itertools.combinations(range(len(E)), 2):
    X, Y = E[a], E[b]; N = X & Y
    if len(N) != 5: continue
    npair += 1
    sing = {}
    for F in E:
        if len(F & N) == 1: sing.setdefault(next(iter(F & N)), set()).add((frozenset(F & (X - N)), frozenset(F & (Y - N))))
    types = len(sing)
    allparts = set().union(*sing.values()) if sing else set()
    if types == 5 and len(allparts) == 1: nuni += 1
    # OD: some part shared by >= 2 types
    from collections import Counter
    cnt = Counter(p for t in sing for p in sing[t])
    if any(v >= 2 for v in cnt.values()) and len(allparts) > 1: nod += 1
print(f'PG(2,4) skeleton: edges={len(E)} 5-pairs={npair} uniform (U1 hyp)={nuni} one-deviant-type (OD hyp)={nod}')
