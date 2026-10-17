"""Test the r=16 / tau=4 analogues of Lemmas A, R, S on the EHT witness H(16,10,7) (literal hypergraph).
Analogue: window 45; t=3 (tau>=4); min pair intersection must be exactly 4; for a 4-pair (E,E'), M=E&E':
every edge meets M; singles F (|F&M|=1) have |F&E|=|F&E'|=4, outside part size 16-1-3-3=9, cross-type disjoint;
Lemma S(c): |A_G&A_H|=1 => C_G=C_H."""
import itertools
r, k, q = 16, 10, 7
core = list(range(k)); nxt = k; E = []
for Y in itertools.combinations(core, q):
    E.append(frozenset(Y) | frozenset(range(nxt, nxt + r - q))); nxt += r - q
print('edges', len(E))
mins = min(len(a & b) for a, b in itertools.combinations(E, 2)); print('min pair', mins)
ok = True; npairs = 0; nsing = 0
for E1, E2 in itertools.combinations(E, 2):
    if len(E1 & E2) != 4: continue
    npairs += 1
    M = E1 & E2; U = E1 | E2
    assert all(F & M for F in E)
    sing = [F for F in E if len(F & M) == 1]
    for F in sing:
        nsing += 1
        if not (len(F & E1) == 4 and len(F & E2) == 4 and len(F - U) == 9): ok = False
    for F, G in itertools.combinations(sing, 2):
        if F & M != G & M:
            if (F - U) & (G - U): ok = False
            AF, AG, CF, CG = F & (E1 - M), G & (E1 - M), F & (E2 - M), G & (E2 - M)
            if len(AF & AG) + len(CF & CG) < 4: ok = False
            if len(AF & AG) == 1 and CF != CG: ok = False
    if npairs > 300: break
print('4-pairs tested', npairs, 'single incidences', nsing, 'all rigidity statements hold:', ok)
