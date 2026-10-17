"""Wave 13: leverage of tau-edges. For each orbit of core 4-sets B (symmetry group of base + first-gen single set, order 576:
S3(gamma) x S2(alpha) x S3(m3) x S2(a3) x S2(a4), and sigma = (P2 P3): v<->w, a3<->a4, c3<->c4), the avoider J of B
(exists by tau>=5) is enumerated as states (b, o) with o_i in [L_i, L_i+3] (a sound SUBSET search is NOT needed for soundness of
'survivors'; see note), filtered by w13_enum.check, then pairwise arc-consistent against the 24 AC-reduced single domains
(w13_dom_ac.json) using the same sound pairwise rules as w13_ac.compat (+ same-pair rules when J is itself a single of the
single's base pair with a different type).
NOTE on completeness: o_i is truncated at L_i+3, so '0 survivors' would NOT be a proof; the run is a ranking heuristic.
"""
import json, itertools, sys, numpy as np
from w13_enum import *
import w13_ac as AC
Dac = json.load(open('w13_dom_ac.json'))
FEAS = json.load(open('w13_feas.json'))
keys = list(Dac)
OS = np.array(OSZ); PC = AC.PC
arrS = {}
for k in keys:
    b = np.array([s[0] for s in Dac[k]], dtype=np.int64); o = np.array([s[1] for s in Dac[k]], dtype=np.int64)
    arrS[k] = (b, o, 21 - PC[b] - o.sum(1))
idx = {s: a for a, s in enumerate(NAMES)}
def perm_from(mp):
    p = list(range(n))
    for a, b_ in mp.items(): p[idx[a]] = idx[b_]
    return p
gens = [perm_from({'g0': 'g1', 'g1': 'g0'}), perm_from({'g0': 'g1', 'g1': 'g2', 'g2': 'g0'}), perm_from({'al0': 'al1', 'al1': 'al0'}),
        perm_from({'m0': 'm1', 'm1': 'm0'}), perm_from({'m0': 'm1', 'm1': 'm2', 'm2': 'm0'}), perm_from({'a3_0': 'a3_1', 'a3_1': 'a3_0'}),
        perm_from({'a4_0': 'a4_1', 'a4_1': 'a4_0'}),
        perm_from({'v': 'w', 'w': 'v', 'a3_0': 'a4_0', 'a4_0': 'a3_0', 'a3_1': 'a4_1', 'a4_1': 'a3_1', 'c3': 'c4', 'c4': 'c3'})]
def apply(p, B): return sum(1 << p[a] for a in bits(B))
def orbit(B):
    seen = {B}; st = [B]
    while st:
        x = st.pop()
        for g in gens:
            y = apply(g, x)
            if y not in seen: seen.add(y); st.append(y)
    return seen

def j_states(B):
    out = []
    for b in FEAS:
        if b & B: continue
        L = [max(0, 5 - pc(b & P[i])) for i in range(4)]
        for d in itertools.product(range(4), repeat=4):
            o = [L[i] + d[i] for i in range(4)]
            if any(o[i] > OSZ[i] for i in range(4)) or sum(o) + pc(b) > 21: continue
            if not check(b, o): out.append((b, o))
    return out

def compatJ(J, k2):
    """J: (b array, o array). returns bool matrix len(J) x len(dom k2)"""
    b1, o1 = J; u1 = 21 - PC[b1] - o1.sum(1)
    b2, o2, u2 = arrS[k2]
    i2, j2 = int(k2[1]), int(k2[3]); x2 = idx[k2.split(':')[1]]
    Nij = P[i2] & P[j2]
    B1 = b1[:, None]; B2 = b2[None, :]; O1 = o1[:, None, :]; O2 = o2[None, :, :]
    I = B1 & B2
    ovhi = np.minimum(O1, O2).copy(); ovlo = np.maximum(0, O1 + O2 - OS[None, None, :])
    uhi = np.minimum(u1[:, None], u2[None, :])
    ok = np.ones(I.shape, bool)
    # same-pair rules if J is a single of (i2,j2) of another type
    sJ = (b1 & Nij); same = (PC[sJ] == 1) & (sJ != (1 << x2))
    if same.any():
        S = same[:, None]
        okS = np.ones(I.shape, bool)
        for q in range(4):
            if q in (i2, j2): continue
            okS &= ovlo[:, :, q] == 0
        okS &= (I & ~(P[i2] | P[j2]) & ((1 << n) - 1)) == 0
        hi_i = np.where(S, 0, 1)  # placeholder
        ovS = ovhi.copy()
        for q in range(4):
            if q not in (i2, j2): ovS[:, :, q] = 0
        a_hi = PC[I & P[i2] & ~Nij & ((1 << n) - 1)] + ovS[:, :, i2]
        c_hi = PC[I & P[j2] & ~Nij & ((1 << n) - 1)] + ovS[:, :, j2]
        okS &= (a_hi >= 2) & (c_hi >= 2) & (a_hi + c_hi >= 5)
        okS &= (PC[I] + ovS.sum(2)) >= 5
        ok &= ~S | okS
    maxI = PC[I] + ovhi.sum(2) + uhi
    ok &= maxI >= 5
    for q in range(4):
        ok &= (PC[I & P[q]] > 0) | (ovhi[:, :, q] >= 1)
    for (k, l), Nkl in AC.NKL.items():
        m = (I & Nkl) == 0
        out = ~(P[k] | P[l]) & ((1 << n) - 1)
        s1 = 9 - (PC[B1 & (P[k] | P[l])] + O1[:, :, k] + O1[:, :, l])
        s2 = 9 - (PC[B2 & (P[k] | P[l])] + O2[:, :, k] + O2[:, :, l])
        lo = PC[I & out] + sum(ovlo[:, :, q] for q in range(4) if q not in (k, l))
        # D1 only gives s>=0 when N_kl not inside the edge; if J contains N_kl, OO still holds as L (no D1 needed)
        ok &= ~m | (lo <= s1 + s2)
    for T, t in TRI.items():
        m = (I & t) == 0
        nn = [q for q in range(4) if q not in T][0]
        U3 = P[T[0]] | P[T[1]] | P[T[2]]
        f1 = PC[B1 & U3] + sum(O1[:, :, q] for q in T); f2 = PC[B2 & U3] + sum(O2[:, :, q] for q in T)
        ok &= ~m | (ovlo[:, :, nn] <= 29 + PC[t] - f1 - f2)
    for (BA, OA, BB, OB) in ((B1, O1, B2, O2), (B2, O2, B1, O1)):
        for k in range(4):
            five = (PC[BA & P[k]] + OA[:, :, k]) == 5
            notin = ((BA & P[k] & ~BB) != 0) | (OA[:, :, k] > OB[:, :, k])
            lo = PC[I & ~P[k] & ((1 << n) - 1)] + sum(ovlo[:, :, q] for q in range(4) if q != k)
            ok &= ~(five & notin) | (PC[BB & P[k]] + OB[:, :, k] + lo <= 9)
    return ok

if __name__ == '__main__':
    reps = []; done = set()
    for Bt in itertools.combinations(range(n), 4):
        B = sum(1 << a for a in Bt)
        if B in done: continue
        orb = orbit(B); done |= orb; reps.append((B, len(orb)))
    print('orbits', len(reps), flush=True)
    sel = sys.argv[1] if len(sys.argv) > 1 else None
    res = {}
    try: res = json.load(open('w13_tau_res.json'))
    except Exception: pass
    import time; t0 = time.time()
    for B, osz in reps:
        if nm(B) in res: continue
        if time.time() - t0 > 95: break
        Js = j_states(B)
        if not Js: res[nm(B)] = dict(orbit=osz, nJ=0); continue
        jb = np.array([s[0] for s in Js], dtype=np.int64); jo = np.array([s[1] for s in Js], dtype=np.int64)
        alive = np.ones(len(Js), bool); blockers = {}
        for k in keys:
            M = compatJ((jb, jo), k)
            sup = M.any(1)
            blockers[k] = int((~sup).sum())
            alive &= sup
        surv = [Js[i] for i in np.nonzero(alive)[0]]
        AND = (1 << n) - 1; OR = 0
        for b, o in surv: AND &= b; OR |= b
        res[nm(B)] = dict(orbit=osz, nJ=len(Js), nJtr=len(set(b for b, o in Js)), surv=len(surv),
                          survtr=len(set(b for b, o in surv)), forced=nm(AND) if surv else None,
                          top_blockers=sorted(blockers.items(), key=lambda kv: -kv[1])[:4])
        print(nm(B), res[nm(B)], flush=True)
        json.dump(res, open('w13_tau_res.json', 'w'))
    json.dump(res, open('w13_tau_res.json', 'w'))
    print('done', len(res), 'of', len(reps))
