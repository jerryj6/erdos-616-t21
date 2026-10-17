from venn2 import *
import itertools
def ex(mval):
    def f(m, c, k):
        full = 1 << k
        for i, j in itertools.combinations(range(k), 2):
            I = (1<<i)|(1<<j)
            e = sum(c[T] for T in range(1, full) if T & I == I)
            m.Add(e >= mval)
            if (i,j)==(0,1): m.Add(e == mval)
    return f
# m=6,7,8: edge2 avoids 4 of M; |M & E2| = s in 1..m-4 (>=1 forced by L); edges 3_s avoid all of M&E2 (exact s) + (4-s) of M\E2
for mval in (6,):
    pats = {2: [(B(0,1),0,4)]}
    k = 3
    for s_ in range(1, min(4, mval-4)+1):
        pats[k] = [(B(0,1,2),0,s_,True), (B(0,1),B(2),4-s_)] if s_<4 else [(B(0,1,2),0,4,True)]
        k += 1
    st, sol, t = run(k, pats, 400, five_pair=False, extra=ex(mval)); print(mval, k, st, round(t,1), flush=True)
