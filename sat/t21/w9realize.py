"""Literal realization of a w9run STALL solution: python3 w9realize.py w9_TAG_stall.json
U-structure: triples of new edges without a common named point get one shared U-point (F1); remaining pair
U-overlaps get pair-private U-points; then every edge is filled to 21 with fresh private points.
Literal checks (plain set arithmetic): sizes, Lemma A, L on EVERY subfamily (DFS, prune at union > 60, exact),
W7-I (no 5-pair has cross-type singles with a = 1 or c = 1), NK (if branch nok4), and closure: for every 5-pair
among edges of gen <= 1, every type has a single in the family (reports the missing ones)."""
import sys, json, itertools
d = json.load(open(sys.argv[1])); names = d['names']
base = [frozenset(names[a] for a in b) for b in d['base']]
new = [set(names[a] for a in e['pts']) for e in d['edges']]
gens = [0] * len(base) + [e['gen'] for e in d['edges']]
labels = [f'B{i}' for i in range(len(base))] + [e['label'] for e in d['edges']]
yu = {(p, q): v for p, q, v in d['yu']}
budget = dict(yu); uid = 0
for p, q, r in itertools.combinations(range(len(new)), 3):
    if new[p] & new[q] & new[r]: continue
    pairs = [(p, q), (p, r), (q, r)]
    if all(budget.get(x, 0) > 0 for x in pairs):
        pt = f'U{uid}'; uid += 1
        for t in (p, q, r): new[t].add(pt)
        for x in pairs: budget[x] -= 1
for (p, q), v in budget.items():
    for _ in range(v):
        pt = f'U{uid}'; uid += 1; new[p].add(pt); new[q].add(pt)
over = [(labels[4 + i], len(E)) for i, E in enumerate(new) if len(E) > 21]
fresh = 0
for E in new:
    while len(E) < 21: E.add(f'z{fresh}'); fresh += 1
E = list(base) + [frozenset(x) for x in new]; n = len(E)
print('edges', n, 'U-points', uid, 'oversize edges', over)
small = [(labels[i], labels[j], len(E[i] & E[j])) for i, j in itertools.combinations(range(n), 2) if len(E[i] & E[j]) < 5]
print('Lemma A violations:', len(small), small[:8])
bad = []; nodes = 0
order = sorted(range(n), key=lambda k: k)
def dfs(start, U, I, fam):
    global nodes
    nodes += 1
    if len(fam) >= 2 and not I: bad.append(list(fam)); return
    if len(bad) > 200: return
    for k in range(start, n):
        U2 = U | E[k]
        if len(U2) > 60: continue
        dfs(k + 1, U2, (I & E[k]) if fam else E[k], fam + [k])
dfs(0, frozenset(), frozenset(), [])
print('L: DFS nodes', nodes, 'violations (empty intersection, union <= 60):', len(bad), [[labels[k] for k in f] for f in bad[:6]])
fp = [(i, j) for i, j in itertools.combinations(range(n), 2) if len(E[i] & E[j]) == 5]
w7 = []; nk = []; missing = []
for i, j in fp:
    N = E[i] & E[j]; sing = {}
    for k in range(n):
        if k in (i, j): continue
        t = E[k] & N
        if len(t) == 1: sing.setdefault(next(iter(t)), []).append(k)
    for t1, t2 in itertools.combinations(sing, 2):
        for a in sing[t1]:
            for b in sing[t2]:
                A = len(E[a] & E[b] & (E[i] - N)); C = len(E[a] & E[b] & (E[j] - N))
                if A == 1 or C == 1: w7.append((labels[i], labels[j], labels[a], labels[b], A, C))
                if len(E[a] & E[b]) < 6: nk.append((labels[i], labels[j], labels[a], labels[b], len(E[a] & E[b])))
    if max(gens[i], gens[j]) <= 1:
        miss = [x for x in N if x not in sing]
        if miss: missing.append((labels[i], labels[j], sorted(N), miss))
print('5-pairs', len(fp), '| W7-I violations', len(w7), w7[:4])
print('NK violations (relevant only in N-noK4)', len(nk), nk[:4])
print('5-pairs among gen<=1 edges with a type lacking a single:', len(missing), missing[:6])
json.dump(dict(labels=labels, edges=[sorted(x) for x in E]), open(sys.argv[1].replace('_stall.json', '_realized.json'), 'w'))
