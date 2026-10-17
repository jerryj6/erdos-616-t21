r"""INDEPENDENT exact re-check of Wave 11e certificates (w11e_certs/c*.json). Imports neither w11_benders nor w11e_oracle.
Base sets from w8k4.base_named('3211'); slot pair labels from w11_meta2.json (full indexing 0..23).
For each certificate: every row is re-derived from the stored traces b* with plain frozenset arithmetic (condition of the
lemma instance holds at b*, stored rhs == recomputed rhs), y >= 0, kappa >= 0, for EVERY allowed column S (nonempty
subset of E, no two slots of one base pair) sum_r y_r coef_r(S) <= sum_{F in S} kappa_F, and the gap is > 0, exactly.
Row semantics (all: sum_S coef(S) n_S >= rhs, n_S = # outside points in exactly the slots S):
  A (F,G): +[F,G in S] >= 5-|bF&bG|>0      T (F,G,H): +[all in S] >= 1, bF&bG&bH empty
  L (B',N'): +[S meets N'] >= 61-|cupB' u cup b_N'| > 0, capB' & cap b_N' empty
  at a 5-pair (P_k,F) (|bF & P_k| = 5, N = bF & P_k):
  D1 (k,F,L): -[F,L in S] >= -(9-|bL & (P_k u bF)|),  N not<= bL
  R3 (k,F,L): -[F,L in S] >= -(5-|bL & bF|),  |bL & N| = 1;   R3B (k,F,L): 0 >= 1 needs |bL&N|=1 and |bL & P_k| > 5
  R3P (k,F,m): 0 >= 1 needs |P_m & N| = 1 and |P_m & bF| > 5;   D1B (k,F,m): 0 >= |P_m & (P_k u bF)| - 9 > 0, N not<= P_m
  SA (k,F,L,M): -[L,M in S, F not in S] >= |bL&bM \ (P_k u bF)|;  L,M singles of (P_k,F) with different N-points
  W7F (k,F,L,M): +[F,L,M in S] >= 2-|bL&bM&bF \ P_k|;  W7P: 0 >= 2-|bL&bM&P_k \ bF| > 0;  same single condition.
  L0 (N'): +[S meets N'] >= 61-|cup b_N'| > 0; |N'| >= 3, two slots of N' with the same base pair, cap b_N' empty.
Also provides holds(cert, bb): the cut's semantic content at traces bb (for encoder tests)."""
import sys, os, json, glob, itertools
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
from w8k4 import base_named, PAT
pts, _ = base_named(PAT['3211']); assert len(pts) == 61
BASE = [frozenset(a for a in range(61) if k in pts[a][1]) for k in range(4)]
META = json.load(open(os.path.join(HERE, 'w11_meta2.json'))); assert META['names'] == [p[0] for p in pts]

def single_pt(bL, N):
    t = bL & N
    return next(iter(t)) if len(t) == 1 else None

def row_check(k, key, r, b):
    """recompute (rhs, coef function) for a row at traces b; raise if the instance is not valid at b."""
    if k == 'A':
        F, G = key; rr = 5 - len(b[F] & b[G]); assert rr > 0
        return rr, (lambda S: 1 if F in S and G in S else 0)
    if k == 'T':
        F, G, H = key; assert not (b[F] & b[G] & b[H])
        return 1, (lambda S: 1 if F in S and G in S and H in S else 0)
    if k == 'L':
        Bp, Np = key; assert Bp and Np
        I = frozenset.intersection(*[BASE[i] for i in Bp]); U = frozenset().union(*[BASE[i] for i in Bp])
        for F in Np: I &= b[F]; U |= b[F]
        assert not I; rr = 61 - len(U); assert rr > 0
        return rr, (lambda S: 1 if any(x in S for x in Np) else 0)
    if k == 'L0':
        Np = key; assert len(Np) >= 3 and len({tuple(META['slots'][F]['pair']) for F in Np}) < len(Np)
        assert not frozenset.intersection(*[b[F] for F in Np]); rr = 61 - len(frozenset().union(*[b[F] for F in Np])); assert rr > 0
        return rr, (lambda S: 1 if any(x in S for x in Np) else 0)
    kk, F = key[0], key[1]; Pk = BASE[kk]; N = b[F] & Pk; assert len(N) == 5, '(P_k,F) not a 5-pair'
    U = Pk | b[F]
    if k == 'D1':
        L = key[2]; assert L != F and not N <= b[L]
        return -(9 - len(b[L] & U)), (lambda S: -1 if F in S and L in S else 0)
    if k == 'R3':
        L = key[2]; assert L != F and single_pt(b[L], N) is not None
        return -(5 - len(b[L] & b[F])), (lambda S: -1 if F in S and L in S else 0)
    if k == 'R3B':
        L = key[2]; assert L != F and single_pt(b[L], N) is not None and len(b[L] & Pk) > 5
        return 1, (lambda S: 0)
    if k == 'R3P':
        m = key[2]; assert m != kk and len(BASE[m] & N) == 1 and len(BASE[m] & b[F]) > 5
        return 1, (lambda S: 0)
    if k == 'D1B':
        m = key[2]; assert m != kk and not N <= BASE[m]; rr = len(BASE[m] & U) - 9; assert rr > 0
        return rr, (lambda S: 0)
    L, M = key[2], key[3]; x, y = single_pt(b[L], N), single_pt(b[M], N)
    assert F not in (L, M) and L != M and x is not None and y is not None and x != y
    if k == 'SA':
        return len((b[L] & b[M]) - U), (lambda S: -1 if L in S and M in S and F not in S else 0)
    if k == 'W7F':
        return 2 - len((b[L] & b[M] & b[F]) - Pk), (lambda S: 1 if F in S and L in S and M in S else 0)
    if k == 'W7P':
        rr = 2 - len((b[L] & b[M] & Pk) - b[F]); assert rr > 0
        return rr, (lambda S: 0)
    raise AssertionError('unknown row kind ' + k)

def norm_key(k, key):
    if k == 'L': return (tuple(key[0]), tuple(key[1]))
    return tuple(key)

def check(c):
    E = [int(F) for F in c['E']]; b = {int(F): frozenset(v) for F, v in c['traces'].items()}
    pair = {int(F): tuple(META['slots'][int(F)]['pair']) for F in E}
    for F in E: assert list(c['pairs'][str(F)]) == list(pair[F]) and len(b[F]) <= 21
    rows = []
    for k, key, r, y in c['rows']:
        y = Fraction(y); assert y >= 0
        key = norm_key(k, key); rr, cf = row_check(k, key, r, b); assert rr == r, ('rhs', k, key, r, rr)
        rows.append((rr, cf, y))
    kap = {int(F): Fraction(v) for F, v in c['kap'].items()}; assert all(v >= 0 for v in kap.values())
    ncol = 0
    for mm in range(1, len(E) + 1):
        for S in itertools.combinations(E, mm):
            if len({pair[F] for F in S}) < len(S): continue
            ncol += 1
            assert sum(y * cf(S) for rr, cf, y in rows) <= sum(kap.get(F, 0) for F in S), ('column', S)
    gap = sum(y * rr for rr, cf, y in rows) - sum(kv * (21 - len(b[F])) for F, kv in kap.items())
    assert gap > 0 and gap == Fraction(c['gap'])
    return ncol, gap

def holds(c, bb):
    """True iff the cut clause's disjunction holds at traces bb (slot -> frozenset): some supported row's validity
    condition fails or its rhs is weaker than at b*, or some kappa>0 slot has |bb_F| < |b*_F|."""
    bs = {int(F): frozenset(v) for F, v in c['traces'].items()}
    for k, key, r, y in c['rows']:
        key = norm_key(k, key)
        try:
            rr, cf = row_check(k, key, None, bb)
        except AssertionError:
            return True                       # condition fails at bb
        if k in ('D1', 'R3', 'R3B', 'R3P', 'D1B', 'SA', 'W7F', 'W7P'):
            # the validity condition must be the SAME instance: same N, same single points
            kk, F = key[0], key[1]
            if (bb[F] & BASE[kk]) != (bs[F] & BASE[kk]): return True
            N = bs[F] & BASE[kk]
            if k in ('R3', 'R3B'):
                if (bb[key[2]] & N) != (bs[key[2]] & N): return True
            if k in ('SA', 'W7F', 'W7P'):
                if (bb[key[2]] & N) != (bs[key[2]] & N) or (bb[key[3]] & N) != (bs[key[3]] & N): return True
        rs, _ = row_check(k, key, None, bs)
        if k in ('R3B', 'R3P'):
            pass                              # rhs constant 1; the condition (>5) is part of row_check
        elif rr < rs: return True             # weaker rhs at bb
        if k == 'L':
            pass
    for F in c['kap']:
        if len(bb[int(F)]) <= len(bs[int(F)]) - 1: return True
    return False

def gd1_violated(g, bb):
    """GD1 instance (k,F,L) at traces bb: True iff the guard fails AND the inequality fails (i.e. the cut is violated).
    Lemma (D1 at the 5-pair (P_k,F) + Lemma A for (F,L)): if |bF & P_k| = 5 and N = bF & P_k not<= bL, then
    GD1a |bL & P_k \\ bF| <= 4 and GD1b |bL & (P_k u bF)| <= 9."""
    Pk = BASE[g['k']]; F, L = g['F'], g['L']
    if len(bb[F] & Pk) >= 6: return False      # (the cut's guard; |bF & P_k| >= 5 holds by Lemma A in every real configuration)
    if (bb[F] & Pk) <= bb[L]: return False
    if g['kind'] == 'GD1a': return len((bb[L] & Pk) - bb[F]) > 4
    return len(bb[L] & (Pk | bb[F])) > 9

def check_gd1(c):
    g = c['generic']; bs = {int(F): frozenset(v) for F, v in c['traces'].items()}
    assert g['kind'] in ('GD1a', 'GD1b') and g['F'] != g['L'] and gd1_violated(g, bs), 'GD1 not violated at stored traces'

def holds_gd1(c, bb):
    return not gd1_violated(c['generic'], bb)

if __name__ == '__main__':
    files = sorted(glob.glob(os.path.join(HERE, 'w11e_certs', 'c*.json')), key=lambda p: int(os.path.basename(p)[1:-5]))
    from collections import Counter
    kinds = Counter(); sizes = Counter(); ngen = 0
    import random; from w11b_recheck import check_generic; rng = random.Random(7)
    for p in files:
        c = json.load(open(p)); sizes[len(c['E'])] += 1
        if c.get('generic') and c['generic']['kind'].startswith('GD1'): check_gd1(c); ngen += 1; continue
        if c.get('generic'): check_generic(c, rng); ngen += 1; continue   # trace-free GEN2/GEN3 (w11b_recheck)
        check(c)
        for k, *_ in c['rows']: kinds[k] += 1
    print(f'w11e certificates re-checked exactly: {len(files)}/{len(files)} OK ({ngen} generic); |E| {dict(sorted(sizes.items()))}; row kinds {dict(kinds)}')
