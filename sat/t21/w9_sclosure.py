r"""Wave 9: S-rigidity closure from ONE uniform 5-pair (sound, uses only Lemma A, F1 and L on 4-families).
S = N(0..4) u A0(5..8) u C0(9..12).  A 'good' edge is an edge P with P∩S = S\D_P (|D_P| = 4) whose outside part
P\S (12 points) is disjoint from the outside part of every other good edge.  Start: X (D=C0), Y (D=A0), F_z (D=N\z).
For a 4-set D, a generic edge E avoiding D has S-part e ⊆ S\D and o_i := |E ∩ (P_i\S)|.  Necessary conditions:
  Lemma A:  |e \ D_i| + o_i >= 5                                  (so o_i >= max(0, 5-|e\D_i|) =: m_i)
  capacity: sum_i o_i <= 21 - |e|                                  (good outsides pairwise disjoint)
  F1:       e ∩ (S \ (D_i ∪ D_j)) ≠ ∅  for all good i<j            (E∩P_i∩P_j ⊆ S since outsides disjoint)
  L4:       if e ⊆ D_i∪D_j∪D_l (so {P_i,P_j,P_l,E} has empty intersection):
            |e \ I| + o_i+o_j+o_l <= |S\I| + 36 + 21 - 61 - ... i.e. |(S\e)\I| >= 4 + o_i+o_j+o_l,  I = D_i∩D_j∩D_l.
All o_i appear only with + in '<=' constraints, so o_i = m_i is the best choice: a pattern e is possible iff it passes with o = m.
D is RIGID if the only possible pattern is e = S\D; the new edge is GOOD if moreover raising any single o_j to 1 breaks a
constraint (so its outside misses every good outside).  Iterate.  Prints the closure and whether a W6-U 'bad family'
(4 good D's = {s0} ∪ R_i, R_i a partition of S\{s0}) is reached."""
import itertools, sys, os
NK = os.environ.get('NK','0')=='1'
S = (1 << 13) - 1
pc = lambda x: bin(x).count('1')
def m(*xs):
    r = 0
    for x in xs: r |= 1 << x
    return r
N = list(range(5)); A0 = m(5, 6, 7, 8); C0 = m(9, 10, 11, 12); Nm = m(*N)
good = [C0, A0] + [Nm & ~(1 << z) for z in N]
names = {C0: 'X', A0: 'Y'}
for z in N: names[Nm & ~(1 << z)] = f'F{z}'

def check(e, good, extra=None):
    """return True iff pattern e passes all constraints (with o = minimal, plus optional o_j += 1)."""
    if pc(e & Nm) == 1 and (e & (A0 | C0)) != (A0 | C0): return False      # (X,Y) uniform
    o = [max(0, 5 - pc(e & ~D)) for D in good]
    if extra is not None: o[extra] += 1
    if sum(o) > 21 - pc(e): return False
    g = len(good)
    U = [S & ~(good[i] | good[j]) for i in range(g) for j in range(i)]
    for i in range(g):
        for j in range(i):
            if e & S & ~(good[i] | good[j]) == 0: return False
    for i in range(g):
        for j in range(i):
            if pc(good[i] | good[j]) == 8:          # (P_i,P_j) is a 5-pair, N_ij = S\(D_i∪D_j)
                Nij = S & ~(good[i] | good[j])
                if (e & Nij) != Nij and pc(e & ~(good[i] & good[j])) + o[i] + o[j] > 9: return False   # D1
                if pc(e & Nij) == 1:   # E is a single of (P_i,P_j); compare with good singles of other types (NT / NK)
                    for l in range(g):
                        if l in (i, j): continue
                        Pl = S & ~good[l]
                        if pc(Pl & Nij) != 1 or (Pl & Nij) == (e & Nij): continue
                        a = pc(e & Pl & (S & ~good[i]) & ~Nij); c = pc(e & Pl & (S & ~good[j]) & ~Nij)
                        if a < 2 or c < 2: return False
                        if NK and a + c < 6: return False
    for i, j, l in itertools.combinations(range(g), 3):
        Ui = good[i] | good[j] | good[l]
        if e & ~Ui: continue
        I = good[i] & good[j] & good[l]
        if pc((S & ~e) & ~I) < 4 + o[i] + o[j] + o[l]: return False
    return True

def status(D, good):
    free = [b for b in range(13) if not (D >> b) & 1]
    pats = []
    for k in range(1 << 9):
        e = 0
        for t, b in enumerate(free):
            if (k >> t) & 1: e |= 1 << b
        if check(e, good): pats.append(e)
    return pats

it = 0
while True:
    it += 1; new = []
    gs = set(good)
    for Dt in itertools.combinations(range(13), 4):
        D = m(*Dt)
        if D in gs: continue
        pats = status(D, good)
        full = S & ~D
        if pats == [full]:
            isgood = all(not check(full, good, extra=j) for j in range(len(good)))
            new.append((D, isgood))
    print(f'iter {it}: good={len(good)} newly rigid={len(new)} of which good={sum(g for _, g in new)}', flush=True)
    add = [D for D, g in new if g]
    if not add: break
    good += add
print('final good D count:', len(good))
for D in good: print(sorted(b for b in range(13) if (D >> b) & 1), names.get(D, ''))
# bad family?
gs = set(good)
found = None
for s0 in range(13):
    rest = [b for b in range(13) if b != s0]
    def parts(lst):
        if not lst: yield []; return
        a = lst[0]
        for p in itertools.combinations(lst[1:], 2):
            R = (a,) + p
            rem = [x for x in lst if x not in R]
            for q in parts(rem): yield [R] + q
    for P in parts(rest):
        if all(m(s0, *R) in gs for R in P): found = (s0, P); break
    if found: break
print('W6-U bad family reachable:', found)
