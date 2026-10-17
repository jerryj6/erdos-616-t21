"""Wave 13: minimum transversals of a realized config and 4-sets of named points covering the most of them.
usage: python3 w13_mintrans.py w10x_TAG_real.json [k]"""
import sys, json, itertools, collections
d = json.load(open(sys.argv[1])); E = [frozenset(x) for x in d['edges']]
P = sorted(frozenset().union(*E)); names = d.get('names') or []
named = [p for p in P if isinstance(p, str) and p[0] in 'Tp'] if names else []
for t in range(1, 5):
    T = [S for S in itertools.combinations(P, t) if all(e & set(S) for e in E)]
    if T: break
print('tau', t, 'num min transversals', len(T))
print('min transversals', T[:40])
c = collections.Counter(p for S in T for p in S); print('point freq', c.most_common(12))
if t <= 3:
    pool = sorted(c)
    best = []
    for B in itertools.combinations(pool, 4):
        k = sum(set(S) <= set(B) for S in T); best.append((k, B))
    best.sort(reverse=True); print('4-sets covering most min transversals', best[:12])
