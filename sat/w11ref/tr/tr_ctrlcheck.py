"""re-check a SAT model of a control Φ directly (no CNF reuse): read the kissat model (NAME.kout 'v' lines), take the
true traces, check (1) every needed 4-set has a true avoider, (2) no two true traces conflict under the CONTROL's rules
(recomputed with tr_core), (3) how many true traces are outside the full (3,3) universe st_FULL.npz and how many true
pairs conflict under the FULL rules.  usage: python3 tr_ctrlcheck.py NAME TAG DROP FULLTAG"""
import sys, itertools, numpy as np
from tr_core import trace_pair_compat
name, tag, drop, ftag = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
fl = lambda t: (1 if 'n' in t else 0) | (2 if 'x' in t else 0) | (4 if 'k' in t else 0) | (8 if 'w' in t else 0)
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
FULL = int(P[0] | P[1] | P[2] | P[3])
lits = [int(x) for l in open(f'{name}.kout') if l.startswith('v') for x in l.split()[1:]]
true = sorted(x - 1 for x in lits if x > 0)
need = [B for B in (sum(1 << x for x in c) for c in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))]
Tb = tr[true]
print(name, 'true traces', len(true), 'COV satisfied', all(((Tb & B) == 0).any() for B in need))
# minimal cover: greedily drop traces keeping all COV (smaller set to inspect)
keep = list(range(len(true)))
for i in sorted(keep, key=lambda i: -bin(int(Tb[i])).count('1')):
    rest = [j for j in keep if j != i]
    if all(((Tb[rest] & B) == 0).any() for B in need): keep = rest
cover = [true[i] for i in keep]
c1 = sum(1 for a, b in itertools.combinations(cover, 2)
         if not trace_pair_compat(a, b, U['first'], U['cnt'], U['SB'], U['SO'], P, U['OS'], FULL, fl(tag), drop))
print('minimal cover', len(cover), 'conflicts under control rules', c1)
F = np.load(f'st_{ftag}.npz'); lut = {int(t): i for i, t in enumerate(F['tr'])}
outside = [int(tr[i]) for i in cover if int(tr[i]) not in lut]
inside = [lut[int(tr[i])] for i in cover if int(tr[i]) in lut]
c2 = sum(1 for a, b in itertools.combinations(inside, 2)
         if not trace_pair_compat(a, b, F['first'], F['cnt'], F['SB'], F['SO'], F['P'], F['OS'], FULL, fl(ftag), 0))
print('cover traces outside the full universe', len(outside), '| full-rule conflicts among the rest', c2)
