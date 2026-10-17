"""Wave 10: exact (integer) re-check of the three hand refutations of W9/W10 stall cores.
(1) SQ on w9_cpt_gen1_stall.json: W=(B2,B1):T123_1, V=(B3,B1):T123_0, G_t = the three (B3,B2)-singles of types T123_*.
(2) SF on w9_cn24_gen1_stall.json: P=B3, Z1=(B3,B0):ah1, Z2=(B3,B0):al0, W=g2:(B0,F4):a09.
(3) SF on w10_sq_k4g1_stall.json: P=B1, (B1,B0):p01_0, (B3,B0):T023_0, (B3,B1):T123_1."""
import json, itertools
def load(fn):
    d = json.load(open(fn)); B = [frozenset(b) for b in d['base']]
    E = {e['label']: frozenset(e['pts']) for e in d['edges']}; return d['names'], B, E
nm, B, E = load('w9_cpt_gen1_stall.json'); allB = frozenset().union(*B)
W, V = E['g1:(B2,B1):T123_1'], E['g1:(B3,B1):T123_0']; Gs = [E[f'g1:(B3,B2):T123_{i}'] for i in range(3)]
N12 = B[1] & B[2]
assert len(N12) == 5 and len(W & N12) == 1 and not (W & V & N12)
sW = 9 - len(W & (B[1] | B[2])); sV = 9 - len(V & (B[1] | B[2]))
T = [g for g in Gs if not (W & V & g)]          # no common NAMED point (named = all of B0..B3)
N23 = B[2] & B[3]; assert all(len(g & N23) == 1 for g in Gs) and len({next(iter(g & N23)) for g in Gs}) == 3
print('(1) SQ: s12(W)=%d s12(V)=%d  #G with W&V&G named-empty = %d  ->' % (sW, sV, len(T)), 'CONTRADICTION' if len(T) > sW + sV else 'no')
nm, B, E = load('w9_cn24_gen1_stall.json')
P = B[3]; Z1, Z2, Wg = E['g1:(B3,B0):ah1'], E['g1:(B3,B0):al0'], E['g2:(B0,F4):a09']
N30 = B[3] & B[0]; assert len(N30) == 5 and len(Z1 & N30) == 1 and len(Z2 & N30) == 1 and (Z1 & N30) != (Z2 & N30)
assert not (P & Z1 & Z2 & Wg)
named_union = len(P | Z1 | Z2 | Wg); caps = sum(21 - len(x) for x in (Z1, Z2, Wg))
need1 = max(0, 5 - len(Z1 & Wg)); need2 = max(0, 5 - len(Z2 & Wg))
# Z1,Z2 cross-type singles of (B3,B0): no common point outside B3 u B0, so no common U-point
ub = named_union + caps - need1 - need2
print('(2) SF: named union %d, U capacity %d, forced U-overlaps Z1W>=%d Z2W>=%d -> |union| <= %d' % (named_union, caps, need1, need2, ub), 'CONTRADICTION' if ub <= 60 else 'no')
nm, B, E = load('w10_sq_k4g1_stall.json')
P = B[1]; X1, X2, X3 = E['g1:(B1,B0):p01_0'], E['g1:(B3,B0):T023_0'], E['g1:(B3,B1):T123_1']
assert not (P & X1 & X2 & X3)
named_union = len(P | X1 | X2 | X3); caps = sum(21 - len(x) for x in (X1, X2, X3))
f12 = max(0, 5 - len(X1 & X2)); f13 = max(0, 5 - len(X1 & X3)); f23 = max(0, 5 - len(X2 & X3))
# U-union <= caps - (pair U-overlaps) + (triple U-overlap) <= caps - max over the two largest forced ... use caps - f12 - f13 (triple <= pair 23 overlap is dropped)
ub = named_union + caps - f12 - f13
print('(3) SF: named union %d, U capacity %d, forced X1X2>=%d X1X3>=%d X2X3>=%d -> |union| <= %d' % (named_union, caps, f12, f13, f23, ub), 'CONTRADICTION' if ub <= 60 else 'no')
