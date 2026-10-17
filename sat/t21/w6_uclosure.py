r"""Checks for Lemma W6-U (Case II-U): (1) moves N -> {t} u (B\N), t in N, on 5-subsets of a 9-set B are connected
(complements walk on Kneser K(9,4)); (2) the relative rule B -> S13 \ C (C a 4-subset of B) closes from one 9-set to
all 715 9-subsets of a 13-set (= closure9.py); (3) a bad family S13 \ ({0} u R_i) exists in it (4 sets, empty
intersection, union 12)."""
from itertools import combinations
B = frozenset(range(9)); N0 = frozenset(range(5))
seen = {N0}; fr = [N0]
while fr:
    nf = []
    for N in fr:
        for t in N:
            N2 = frozenset({t}) | (B - N)
            if N2 not in seen: seen.add(N2); nf.append(N2)
    fr = nf
print('reachable 5-subsets of B:', len(seen), 'of 126')
S13 = frozenset(range(13)); start = frozenset(range(9)); F = {start}; fr = [start]
while fr:
    nf = []
    for X in fr:
        for C in combinations(sorted(X), 4):
            Y = S13 - frozenset(C)
            if Y not in F: F.add(Y); nf.append(Y)
    fr = nf
print('closure size:', len(F))
R = [frozenset({1,2,3}), frozenset({4,5,6}), frozenset({7,8,9}), frozenset({10,11,12})]
fam = [S13 - ({0} | r) for r in R]
print('bad family in closure:', all(s in F for s in fam), 'intersection:', set.intersection(*map(set, fam)),
      'union size:', len(frozenset().union(*fam)), '-> span with disjoint 12-point outsides =', len(frozenset().union(*fam)) + 48)
