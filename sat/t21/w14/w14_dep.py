"""Dependency analysis of a verified certificate: which pairwise rule families its CORE conflict clauses need.
Reads a drat-trim core (-c) file; for every binary all-negative clause (-a -b) = conflict pair of traces a-1, b-1, recomputes
the trace-level conflict with w14_compat.compat (a) with all rules (must be a conflict: sanity) and (b) with each family
dropped. Reports, per family, how many core clauses stop being conflicts without it (0 => certificate does not use it).
Usage: python3 w14_dep.py CORE_FILE"""
import sys, json, collections, numpy as np
from w14_compat import compat
FAM = ['SAME', 'A', 'F1', 'OO', 'L3', 'D1d']
D = json.load(open('w14_states.json'))
z = np.load('w14_conf.npz'); T = z['T']; NT = len(T)
SB = [np.array([b] * len(s), dtype=np.int64) for b, s in D]; SO = [np.array(s, dtype=np.int64) for b, s in D]
assert all(int(T[i]) == D[i][0] for i in range(NT))
pairs = []
for line in open(sys.argv[1]):
    if line.startswith('p') or line.startswith('c'): continue
    L = [int(x) for x in line.split()[:-1]]
    if len(L) == 2 and L[0] < 0 and L[1] < 0: pairs.append((-L[0] - 1, -L[1] - 1))
by = collections.defaultdict(list)
for a, b in pairs: by[a].append(b)
need = {f: 0 for f in FAM}; insane = 0; tot = 0
for a, bs in by.items():
    b2 = np.concatenate([SB[b] for b in bs]); o2 = np.concatenate([SO[b] for b in bs])
    owner = np.concatenate([[k] * len(SB[b]) for k, b in enumerate(bs)])
    def conflicts(drop):
        M = compat(SB[a], SO[a], b2, o2, drop).any(0)
        anyc = np.zeros(len(bs), bool); np.logical_or.at(anyc, owner, M)
        return ~anyc
    full = conflicts(())
    insane += int((~full).sum()); tot += len(bs)
    for f in FAM: need[f] += int((full & ~conflicts((f,))).sum())
print('core conflict clauses', tot, 'not conflicts under full rules (must be 0):', insane)
print('core clauses that NEED each family:', need, flush=True)
