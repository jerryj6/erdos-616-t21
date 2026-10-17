"""Realise a solution of the N-K4 point model as an explicit partial hypergraph and check L by exhaustive search.
Each edge is filled up to 21 points with fresh private points.  Checks: every edge has 21 points; the four base
edges form the (3,2,1,1)-K4; L: every subfamily with empty common intersection has union >= 61 (DFS with pruning
at union > 60 is exact: unions only grow).  Also reports pairs with |F&G| < 5 (Lemma A is a GLOBAL consequence of
tau >= 5, not of L, so a partial family may violate it; we report it honestly)."""
import sys, json, itertools
from w8sat import *
pat = sys.argv[1]; flags = sys.argv[2:]
e, X, pts, W = build(pat, None, tt=True)
s = Cadical153(bootstrap_with=e.cl); assert s.solve()
m = set(l for l in s.get_model() if l > 0)
nm = [p[0] for p in pts]
base_edges = [frozenset(nm[a] for a in range(len(pts)) if i in pts[a][1]) for i in range(4)]
edges = list(base_edges); labels = [f'P{i}' for i in range(4)]
fresh = 0
for F in X:
    S_ = set(nm[a] for a in range(len(pts)) if F['b'][a] in m)
    while len(S_) < 21: S_.add(f'u{fresh}'); fresh += 1
    edges.append(frozenset(S_)); labels.append(f"S{F['pair'][0]}{F['pair'][1]}:{nm[F['x']]}")
assert all(len(E) == 21 for E in edges)
print('edges', len(edges), 'pairwise |P_i&P_j|', [len(base_edges[i] & base_edges[j]) for i, j in itertools.combinations(range(4), 2)],
      'K4 union', len(frozenset().union(*base_edges)))
n = len(edges); bad = []; nodes = 0
def dfs(start, U, I, fam):
    global nodes
    nodes += 1
    if len(fam) >= 2 and not I: bad.append(list(fam)); return
    for k in range(start, n):
        U2 = U | edges[k]
        if len(U2) > 60: continue
        dfs(k + 1, U2, (I & edges[k]) if fam else edges[k], fam + [k])
dfs(0, frozenset(), frozenset(), [])
print('DFS nodes', nodes, 'L-violations (empty intersection, union <= 60):', len(bad), [[labels[k] for k in f] for f in bad[:5]])
small = [(labels[i], labels[j], len(edges[i] & edges[j])) for i, j in itertools.combinations(range(n), 2) if len(edges[i] & edges[j]) < 5]
print('pairs meeting in < 5 points:', len(small), small[:10])
json.dump({'labels': labels, 'edges': [sorted(E) for E in edges]}, open(f'w8_realized_{pat}.json', 'w'))
