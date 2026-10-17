"""Completeness of the variable universe: enumerate EVERY core trace b meeting all N_ij over the rigorous o-box of
w14_states.box and confirm that the feasible ones are exactly w13_feas.json (S13.1 restricted o to {L, L+1})."""
import sys, json, itertools
sys.path.insert(0, '..')
from w13_enum import *
from w14_states import box
feas = set(json.load(open('../w13_feas.json')))
found = set(); pts = 0
for b in range(1 << n):
    if not all(b & Nij for Nij in N.values()): continue
    L, U = box(b)
    for o in itertools.product(*[range(L[i], U[i] + 1) for i in range(4)]):
        pts += 1
        if not check(b, list(o)): found.add(b); break
print('box points', pts, 'feasible traces (full box)', len(found), 'w13_feas', len(feas), 'missing from w13_feas', len(found - feas), 'extra', len(feas - found))
