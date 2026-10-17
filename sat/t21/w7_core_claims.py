from w7_core import *
def U(m, Y, k):
    a, b = [i for i in (1,2,3) if i != k]
    u = {}
    for p in Qi[a] + Qi[b]:
        v = m.NewBoolVar(''); u[p] = v
        lits = [Y[a, b, c]['t'][p] for c in range(4)]
        m.AddMaxEquality(v, lits)
    return u
def noA(m, W, Y, oin): pass
claims = {
 'U1=4': lambda m, W, Y, oin: m.Add(sum(U(m, Y, 1).values()) == 4),
 'someE3': lambda m, W, Y, oin: m.Add(sum(w['e3'] for w in W.values()) >= 1),
 'W1_3 e3': lambda m, W, Y, oin: m.Add(W[1,3]['e3'] == 1),
 'Y12_0 |S|=4': lambda m, W, Y, oin: m.Add(sum(Y[1,2,0]['t'][p] for p in Qi[1]+Qi[2]) == 4),
}
for n, f in claims.items():
    print(n, run(f, tl=60), flush=True)
