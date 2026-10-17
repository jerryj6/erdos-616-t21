"""REFEREE: check the non-binary clauses of a case CNF (or certdead CNF) against my own universe.
 * every 4-set B of core points meeting all four base edges ('needed B') must have a clause containing every var whose
   trace (in MY universe) avoids B (extra literals of traces outside my universe are harmless);
 * no positive clause other than COV / the unit / (certdead) the dead-avoider clause;
 * reports the unit clause and its trace.
usage: python3 ref_cov.py CNF"""
import sys, json, itertools, numpy as np
from ref_states import Pm, NAMES, pc
from pairref import read_binary
T = np.load('../w14/w14_conf.npz')['T'].tolist()           # var-1 -> trace (data)
mine = json.load(open('ref_feas.json'))['traces']
lut = {t: i + 1 for i, t in enumerate(T)}
assert all(t in lut for t in mine)
need = [B for B in (sum(1 << a for a in c) for c in itertools.combinations(range(16), 4)) if all(B & Pm[q] for q in range(4))]
print('needed B', len(need))
pa, pb, other = read_binary(sys.argv[1])
clauses = [frozenset(c) for c in other]
pos = [c for c in clauses if all(x > 0 for x in c)]
mixed = [c for c in clauses if not all(x > 0 for x in c)]
print('binary', len(pa), 'nonbinary', len(clauses), 'positive', len(pos), 'non-positive non-binary', len(mixed))
assert not mixed
units = [c for c in pos if len(c) == 1]
cs = set(pos)
ok = 0; miss = []; used = set()
for B in need:
    av = frozenset(lut[t] for t in mine if t & B == 0)
    if av in cs: ok += 1; used.add(av)
    else: miss.append(B)
print('COV(B) present EXACTLY (my avoider list):', ok, 'of', len(need), 'missing', len(miss))
def nm(b): return '{' + ','.join(NAMES[a] for a in range(16) if b >> a & 1) + '}'
for u in units: x = next(iter(u)); print('unit x', x, 'trace', T[x - 1], nm(T[x - 1]))
rest = [c for c in pos if len(c) > 1 and c not in used]
print('other positive clauses:', len(rest), [len(c) for c in rest])
for c in rest: print('  all literals avoid B*={w,g0,g1,g2}:', all(T[x-1] & 0b1110010 == 0 for x in c))
