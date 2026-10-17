"""For every 4-subset B of the core: is a single generic edge avoiding B consistent with the base K4 (Lemma A, F1, D1, L3)?"""
import sys, itertools
from w8sat import *
pat = sys.argv[1]
pts, _ = base_named(PAT[pat]); core = [p[0] for p in pts if not p[0].startswith('O')]
e, X, pts, W = build(pat, sel=[], gen=[()])
s = Cadical153(bootstrap_with=e.cl)
G = X[0]
bad = []
for B in itertools.combinations(range(len(core)), 4):
    if not s.solve(assumptions=[-G['b'][a] for a in B]): bad.append([core[a] for a in B])
print(pat, 'unavoidable 4-sets:', len(bad), bad[:50])
