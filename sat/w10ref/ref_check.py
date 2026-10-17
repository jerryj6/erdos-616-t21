"""Literal (plain set arithmetic) evaluation of the eager statements and of every core instance on a model of ref_enc.py.
usage: python3 ref_check.py CNF   (reads CNF.glucose4.model and CNF.map.json); writes CNF.fix.json and CNF.sat_inst.json /
CNF.viol_inst.json for the exactness/soundness controls."""
import sys, json, itertools, os
sys.argv_saved = list(sys.argv)
cnf = sys.argv[1]
K = 114
# rebuild the same base and variable numbering as ref_enc.py (TRUE=1, then X row-major)
import importlib.util
NN = 61; NP = NN + K
mp = json.load(open(cnf + '.map.json')); jmap = {int(k): v for k, v in mp['jmap'].items()}
mdl = set(int(t) for t in open(cnf + '.glucose4.model').read().split() if int(t) > 0)
X = [[2 + s * NP + a for a in range(NP)] for s in range(19)]
slotsets = [frozenset(a for a in range(NP) if X[s][a] in mdl) for s in range(19)]
# base (same definition, re-typed)
v, w = 0, 1; m = [2, 3, 4]; al = [5, 6]; ag = [7, 8]; ah = [9, 10]; ar = list(range(11, 21)); cl = list(range(21, 25))
cr = list(range(25, 37)); og = list(range(37, 49)); oh = list(range(49, 61))
M = {v, w, *m}
BASE = [frozenset(M | set(al + ag + ah + ar)), frozenset(M | set(cl + cr)), frozenset({v} | set(al + ag + cl + og)),
        frozenset({w} | set(al + ah + cl + oh))]
def E(e):
    if e < 0: return BASE[-1 - e]
    s = jmap[e]; S = slotsets[s]
    return S | frozenset(('p', s, i) for i in range(21 - len(S)))
assert all(len(S) <= 21 for S in slotsets)
def holds(ins):
    k = ins[0].lstrip('X')
    if k == 'L':
        fam = [E(e) for e in ins[1]]
        I = frozenset.intersection(*fam); U = frozenset.union(*fam)
        return bool(I) or len(U) >= 61
    Xs, Ys = E(ins[1]), E(ins[2]); N = Xs & Ys
    if len(N) != 5: return True
    if k == 'R3':
        Z = E(ins[3])
        return len(Z & N) != 1 or (len(Z & Xs) == 5 and len(Z & Ys) == 5)
    if k == 'D1':
        L = E(ins[3])
        return N <= L or len(L & (Xs | Ys)) <= 9
    Z1, Z2 = E(ins[3]), E(ins[4])
    if len(Z1 & N) != 1 or len(Z2 & N) != 1 or (Z1 & Z2 & N): return True
    zz = Z1 & Z2
    if k == 'SA': return zz <= (Xs | Ys)
    if k == 'W7': return len(zz & (Xs - Ys)) >= 2 and len(zz & (Ys - Xs)) >= 2 and ('nonk' in sys.argv or len(zz) >= 6)
core = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 't21', 'w10x_n24s_core.json')))['inst']
sat = [i for i in core if holds(i)]; viol = [i for i in core if not holds(i)]
print('instances satisfied', len(sat), 'violated', len(viol), 'violated kinds', sorted(set(i[0] for i in viol)))
# eager statements, literally
slots = mp['slots']
bad = 0
for s, (i, j, y) in enumerate(slots):
    F = E([t for t, ss in jmap.items() if ss == s][0])
    N = BASE[i] & BASE[j]
    if len(F & N) != 1: bad += 1
    if len(F & BASE[i]) != 5 or len(F & BASE[j]) != 5: bad += 1
    for k in range(4):
        if len(F & BASE[k]) < 5: bad += 1
for t1, t2 in itertools.combinations(range(19), 2):
    F1, F2 = E(t1), E(t2)
    if len(F1 & F2) < 5: bad += 1
    for k in range(4):
        if not (F1 & F2 & BASE[k]): bad += 1
print('eager spot-check violations', bad)
json.dump({str(t): sorted(slotsets[jmap[t]]) for t in range(19)}, open(cnf + '.fix.json', 'w'))
json.dump(sat, open(cnf + '.sat_inst.json', 'w')); json.dump(viol, open(cnf + '.viol_inst.json', 'w'))
