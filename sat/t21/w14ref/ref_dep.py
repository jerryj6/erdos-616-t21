"""REFEREE: family dependency of each certificate's drat-trim core (MY core files drat_<c>.core), under MY checker:
number of core CONF clauses that stop being conflicts when one family is dropped. 0 => the certificate is valid without it."""
import sys, numpy as np
from pairref import load_states, check_pairs, read_binary, P, OS
first, cnt, B, O = load_states('ref_states.npz')
c = sys.argv[1]
pa, pb, other = read_binary(f'drat_{c}.core')
base = check_pairs(pa, pb, first, cnt, B, O, P, OS, 0)
out = [f'case {c} core binary {len(pa)} core nonbinary {len(other)} full-rules disagreements {int((base==1).sum())}']
for nmf, fl in [('A',1),('F1',2),('SAME',4),('OO(L|X|=2)',8),('L|X|=3',16),('L|X|=4',32),('D1d',64),('L3+L4',48)]:
    r = check_pairs(pa, pb, first, cnt, B, O, P, OS, fl)
    out.append(f'  drop {nmf}: {int((r==1).sum())} core clauses lost')
print('\n'.join(out), flush=True)
