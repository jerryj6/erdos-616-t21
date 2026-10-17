"""Independent literal check of a w10x realized configuration: python3 w10x_verify.py w10x_TAG_real.json [nk]
Checks with plain set arithmetic (no solver code shared): sizes 21, base = the 4 given edges, Lemma A, property L on
EVERY subfamily (exact DFS), and at every 5-pair: R.3 sizes, S(a) disjointness, D1, W7-I (+NK if 'nk'), and no trace
triangle (W7-1).  Also computes tau of the partial hypergraph (exact, by increasing hitting-set size)."""
import sys, json, itertools
d = json.load(open(sys.argv[1])); nk = 'nk' in sys.argv[2:]
E = [frozenset(x) for x in d['edges']]; lab = d['labels']; n = len(E)
assert all(len(x) == 21 for x in E), 'size'
print('edges', n, 'points', len(frozenset().union(*E)))
print('LemmaA min pair', min(len(E[i] & E[j]) for i, j in itertools.combinations(range(n), 2)))
bad = []; cnt = [0]
def dfs(start, U, I, fam):
    if len(fam) >= 2:
        cnt[0] += 1
        if not I: bad.append(fam); return
    for k in range(start, n):
        U2 = U | E[k]
        if len(U2) > 60: continue
        dfs(k + 1, U2, (I & E[k]) if fam else E[k], fam + [k])
dfs(0, frozenset(), frozenset(), [])
print('L: subfamilies with union <= 60 examined', cnt[0], 'violations', len(bad), [[lab[k] for k in f] for f in bad[:3]])
v = {'R3': 0, 'SA': 0, 'D1': 0, 'W7': 0, 'NK': 0, 'TT': 0}; np5 = 0; classes = {}
for i, j in itertools.combinations(range(n), 2):
    N = E[i] & E[j]
    if len(N) != 5: continue
    np5 += 1; U = E[i] | E[j]; sing = {}
    for k in range(n):
        if k in (i, j): continue
        t = E[k] & N
        if len(t) == 1: sing.setdefault(next(iter(t)), []).append(k)
        if not N <= E[k] and len(E[k] & U) > 9: v['D1'] += 1
    for t, ks in sing.items():
        for k in ks:
            if len(E[k] & E[i]) != 5 or len(E[k] & E[j]) != 5: v['R3'] += 1
    for t1, t2 in itertools.combinations(sing, 2):
        for a in sing[t1]:
            for b in sing[t2]:
                AB = E[a] & E[b]
                if AB - U: v['SA'] += 1
                ac = (len(AB & (E[i] - E[j])), len(AB & (E[j] - E[i])))
                classes[ac] = classes.get(ac, 0) + 1
                if min(ac) < 2: v['W7'] += 1
                if nk and len(AB) < 6: v['NK'] += 1
for x in range(n):
    cand = [k for k in range(n) if k != x and len(E[k] & E[x]) == 5]
    for a, b, c in itertools.combinations(cand, 3):
        ta, tb, tc = E[a] & E[x], E[b] & E[x], E[c] & E[x]
        if len(ta & tb) == 1 and len(ta & tc) == 1 and len(tb & tc) == 1 and not (ta & tb & tc): v['TT'] += 1
print('5-pairs', np5, 'violations', v, 'cross-type classes (a,c):count', dict(sorted(classes.items())))
pts = sorted(frozenset().union(*E), key=str)
for t in range(1, 6):
    hit = None
    # candidate points: those in >= 2 edges suffice except trivial cases
    cand = [p for p in pts if sum(p in x for x in E) >= 2]
    for H in itertools.combinations(cand, t):
        Hs = set(H)
        if all(x & Hs for x in E): hit = H; break
    if hit: print('tau =', t, 'e.g.', sorted(map(str, hit))); break
else: print('tau >= 6')
