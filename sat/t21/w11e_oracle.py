r"""Wave 11e: EXTENDED outside-point LP oracle = w11_benders' LP (cap, A, T, L; columns: no two slots of one base pair)
PLUS rows for the proved 5-pair lemmas at the DERIVED 5-pairs (P_k, F)  (F a slot with |b_F & P_k| = 5; base edges have
no outside points, so this condition and N' := P_k & b_F are named-only):
  D1  (k,F,L)    L slot, N' not<= b_L :        sum_{S >= {F,L}} n_S <= 9 - |b_L & (P_k u b_F)|          [D1, §6.0]
  D1B (k,F,m)    base P_m, N' not<= P_m :      0 <= 9 - |P_m & (P_k u b_F)|          (named only; row only if violated)
  R3  (k,F,L)    L slot, |b_L & N'| = 1 :      sum_{S >= {F,L}} n_S <= 5 - |b_L & b_F|               [R.3]
  R3B (k,F,L)    same, named side:             |b_L & P_k| = 5                        (named only; row only if > 5)
  R3P (k,F,m)    base P_m, |P_m & N'| = 1 :    |P_m & b_F| = 5                        (named only; row only if > 5)
  SA  (k,F,L,M)  L,M slots, singles of (P_k,F) of different types:
                 sum_{S >= {L,M}, F notin S} n_S + |b_L & b_M \ (P_k u b_F)| <= 0                     [S(a)/R.3]
  W7F (k,F,L,M)  same:  sum_{S >= {F,L,M}} n_S >= 2 - |b_L & b_M & b_F \ P_k|                       [W7-I]
  W7P (k,F,L,M)  same, named side:  |b_L & b_M & P_k \ b_F| >= 2                        (named only; row only if violated)
  L0  (N')       N' subset of slots, |N'| >= 3, two slots of N' are singles of ONE base pair (so by S(a) no outside point
                 lies in all of N'), named intersection of N' empty:  L on N' alone:
                 sum_{S meets N'} n_S >= 61 - |cup b_N'|                                                  [L, S(a)]
Every row reads  sum_S coef_r(S) n_S >= rhs_r  with coef in {-1,0,+1} INDEPENDENT of the traces; the Farkas argument
of w11_benders carries over verbatim (sum y_r coef_r(S) <= sum_{F in S} kappa_F for every column).
CUT literals: for every supported row, 'the row's validity condition fails' OR 'its rhs got weaker'; for kappa>0 edges
'|b_F| <= |b*_F| - 1'.  (Validity conditions: b_F & P_k != N'*, b_L & N'* != {x*}, N'* <= b_L, ...)"""
import itertools
from fractions import Fraction
FULL = (1 << 61) - 1
bc = lambda x: x.bit_count()

def base_sets(base):
    out = []
    for kb in range(1, 5):
        for Bp in itertools.combinations(range(4), kb):
            capB = FULL; cupB = 0
            for i in Bp: capB &= base[i]; cupB |= base[i]
            out.append((Bp, capB, cupB))
    return out

def derived_rows(E, b, base):
    rows = []
    for k in range(4):
        Pk = base[k]
        for F in E:
            Np = b[F] & Pk
            if bc(Np) != 5: continue
            U = Pk | b[F]
            sing = {}
            for L in E:
                if L == F: continue
                if Np & ~b[L]:
                    rows.append(('D1', (k, F, L), -(9 - bc(b[L] & U))))
                t = b[L] & Np
                if bc(t) == 1:
                    sing[L] = t.bit_length() - 1
                    rows.append(('R3', (k, F, L), -(5 - bc(b[L] & b[F]))))
                    if bc(b[L] & Pk) > 5: rows.append(('R3B', (k, F, L), 1))
            for m in range(4):
                if m == k: continue
                if Np & ~base[m]:
                    c = bc(base[m] & U)
                    if c > 9: rows.append(('D1B', (k, F, m), c - 9))
                if bc(base[m] & Np) == 1 and bc(base[m] & b[F]) > 5: rows.append(('R3P', (k, F, m), 1))
            for L, M in itertools.combinations(sorted(sing), 2):
                if sing[L] == sing[M]: continue
                rows.append(('SA', (k, F, L, M), bc(b[L] & b[M] & ~U)))
                rows.append(('W7F', (k, F, L, M), 2 - bc(b[L] & b[M] & b[F] & ~Pk)))
                cP = bc(b[L] & b[M] & Pk & ~b[F])
                if cP < 2: rows.append(('W7P', (k, F, L, M), 2 - cP))
    return rows

def basic_rows(E, b, base, Lmax=None):
    rows = []
    for F, G in itertools.combinations(E, 2):
        r = 5 - bc(b[F] & b[G])
        if r > 0: rows.append(('A', (F, G), r))
    for t in itertools.combinations(E, 3):
        if not (b[t[0]] & b[t[1]] & b[t[2]]): rows.append(('T', t, 1))
    for Bp, capB, cupB in base_sets(base):
        for kn in range(1, (Lmax or len(E)) + 1):
            for Np in itertools.combinations(E, kn):
                I = capB; U = cupB
                for F in Np: I &= b[F]; U |= b[F]
                if I: continue
                r = 61 - bc(U)
                if r > 0: rows.append(('L', (Bp, Np), r))
    return rows

def l0_rows(E, b, pair, maxn=None):
    rows = []
    for kn in range(3, (maxn or len(E)) + 1):
        for Np in itertools.combinations(E, kn):
            if len({tuple(pair[F]) for F in Np}) == kn: continue
            I = FULL; U = 0
            for F in Np: I &= b[F]; U |= b[F]
            if I: continue
            r = 61 - bc(U)
            if r > 0: rows.append(('L0', tuple(Np), r))
    return rows

def coef(kind, key, S):
    if kind in ('A', 'T'): return 1 if all(x in S for x in key) else 0
    if kind == 'L': return 1 if any(x in S for x in key[1]) else 0
    if kind == 'L0': return 1 if any(x in S for x in key) else 0
    if kind in ('D1', 'R3'): return -1 if (key[1] in S and key[2] in S) else 0
    if kind == 'SA': return -1 if (key[2] in S and key[3] in S and key[1] not in S) else 0
    if kind == 'W7F': return 1 if (key[1] in S and key[2] in S and key[3] in S) else 0
    return 0   # named-only rows

def row_slots(kind, key):
    if kind == 'L': return tuple(key[1])
    if kind in ('A', 'T', 'L0'): return tuple(key)
    if kind in ('D1B', 'R3P'): return (key[1],)
    return tuple(key[1:])

def allowed_cols(E, pair):
    by = {}
    for F in E: by.setdefault(tuple(pair[F]), []).append(F)
    cols = []
    for ch in itertools.product(*[[None] + v for v in by.values()]):
        S = tuple(sorted(x for x in ch if x is not None))
        if S: cols.append(S)
    return cols

def lp_cert(E, b, pair, rows):
    """dual LP; exact rational certificate dict, None (feasible) or 'numerr'."""
    from ortools.linear_solver import pywraplp
    E = list(E); cols = allowed_cols(E, pair); cap = {F: 21 - bc(b[F]) for F in E}
    C = [[(i, coef(k, key, S)) for i, (k, key, r) in enumerate(rows) if coef(k, key, S)] for S in cols]
    lp = pywraplp.Solver.CreateSolver('GLOP')
    y = [lp.NumVar(0, 1, '') for _ in rows]; kap = {F: lp.NumVar(0, lp.infinity(), '') for F in E}
    for S, h in zip(cols, C):
        c = lp.Constraint(-lp.infinity(), 0)
        for i, v in h: c.SetCoefficient(y[i], v)
        for F in S: c.SetCoefficient(kap[F], -1)
    obj = lp.Objective()
    for i, (k, key, r) in enumerate(rows): obj.SetCoefficient(y[i], r)
    for F in E: obj.SetCoefficient(kap[F], -cap[F])
    obj.SetMaximization(); lp.Solve()
    if obj.Value() <= 1e-6: return None
    # phase 2 (sparse certificate): min sum y + sum kappa  s.t. column constraints and gap >= 1
    lp2 = pywraplp.Solver.CreateSolver('GLOP')
    y2 = [lp2.NumVar(0, lp2.infinity(), '') for _ in rows]; k2 = {F: lp2.NumVar(0, lp2.infinity(), '') for F in E}
    for S, h in zip(cols, C):
        c = lp2.Constraint(-lp2.infinity(), 0)
        for i, v in h: c.SetCoefficient(y2[i], v)
        for F in S: c.SetCoefficient(k2[F], -1)
    g = lp2.Constraint(1, lp2.infinity())
    for i, (k, key, r) in enumerate(rows): g.SetCoefficient(y2[i], r)
    for F in E: g.SetCoefficient(k2[F], -cap[F])
    o2 = lp2.Objective()
    for v in y2: o2.SetCoefficient(v, 1)
    for v in k2.values(): o2.SetCoefficient(v, 1)
    o2.SetMinimization()
    if lp2.Solve() == pywraplp.Solver.OPTIMAL: y, kap = y2, k2
    for den in (1000, 100000):
        Y = [Fraction(v.solution_value()).limit_denominator(den) if v.solution_value() > 1e-9 else Fraction(0) for v in y]
        K = {F: Fraction(kap[F].solution_value()).limit_denominator(den) if kap[F].solution_value() > 1e-9 else Fraction(0) for F in E}
        for _ in range(4):
            bad = 0
            for S, h in zip(cols, C):
                d = sum(Y[i] * v for i, v in h) - sum(K[F] for F in S)
                if d > 0:
                    bad += 1
                    for F in S: K[F] += d / len(S)
            if not bad: break
        gap = sum(Y[i] * r for i, (k, key, r) in enumerate(rows)) - sum(K[F] * cap[F] for F in E)
        if gap > 0 and all(sum(Y[i] * v for i, v in h) <= sum(K[F] for F in S) for S, h in zip(cols, C)):
            sup = [(k, key, r, Y[i]) for i, (k, key, r) in enumerate(rows) if Y[i] > 0]
            Es = sorted(set(x for k, key, r, yv in sup for x in row_slots(k, key)) | {F for F in E if K[F] > 0})
            return dict(E=Es, rows=sup, kap={F: K[F] for F in E if K[F] > 0}, gap=gap)
    return 'numerr'

def cert_for(E, b, base, pair):
    return lp_cert(E, b, pair, basic_rows(E, b, base) + derived_rows(E, b, base) + l0_rows(E, b, pair))

def scan(b, base, pair, maxk, n, budget, log=print):
    import time
    found = []; t0 = time.time()
    for k in range(2, maxk + 1):
        for E in itertools.combinations(range(n), k):
            if any(set(f) <= set(E) for f in found): continue
            c = cert_for(E, b, base, pair)
            if c == 'numerr': log('  numerr', E); continue
            if c: found.append(tuple(c['E'])); yield c
            if time.time() - t0 > budget: return
        if found: return

# ------------------------------------------------------------------------------------------------ cut encoding
def encode_cut(enc, cert, bs, bvars, base):
    """enc: w11_benders.PEnc (exact cached aux).  bs: list slot -> int mask (traces b*)."""
    cl = []
    bv = lambda F, a: bvars[F][a]
    pr = lambda F, G, a: enc.AND((bv(min(F, G), a), bv(max(F, G), a)))
    def neq_set(F, mask, region):          # literals of 'b_F & region != mask'
        return [(-bv(F, a) if mask >> a & 1 else bv(F, a)) for a in range(61) if region >> a & 1]
    for (k, key, r, yv) in cert['rows']:
        if k == 'A':
            F, G = sorted(key); ks = bc(bs[F] & bs[G])
            cl.append(enc.ge(enc.count(('pair', F, G), [pr(F, G, a) for a in range(61)], max(6, ks + 1)), ks + 1))
        elif k == 'T':
            F, G, H = sorted(key)
            cl.append(enc.OR([enc.AND((pr(F, G, a), bv(H, a))) for a in range(61)]))
        elif k in ('L', 'L0'):
            Bp, Np = key if k == 'L' else ((), key); Np = tuple(sorted(Np)); capB = FULL; cupB = 0
            for i in Bp: capB &= base[i]; cupB |= base[i]
            Us = cupB
            for F in Np: Us |= bs[F]
            inter = [a for a in range(61) if capB >> a & 1]
            if inter: cl.append(enc.OR([enc.AND(tuple(bv(F, a) for F in Np)) for a in inter]))
            out = [a for a in range(61) if not cupB >> a & 1]
            need = bc(Us) + 1 - bc(cupB)
            cl.append(enc.ge(enc.count(('union', cupB, Np), [enc.OR([bv(F, a) for F in Np]) for a in out], need), need))
        else:
            kk, F = key[0], key[1]; Pk = base[kk]; Ns = bs[F] & Pk
            cl += neq_set(F, Ns, Pk)                                   # (P_k,F) no longer the same 5-pair
            if k == 'D1':
                L = key[2]; Ns_ = [a for a in range(61) if Ns >> a & 1]
                cl.append(enc.AND(tuple(bv(L, a) for a in Ns_)))      # N' <= b_L
                c = bc(bs[L] & (Pk | bs[F]))
                lits = [bv(L, a) if Pk >> a & 1 else pr(F, L, a) for a in range(61)]
                cl.append(-enc.ge(enc.count(('d1', kk, F, L), lits, c), c))   # |b_L & (P_k u b_F)| <= c-1
            elif k == 'R3':
                L = key[2]; cl += neq_set(L, bs[L] & Ns, Ns)
                c = bc(bs[L] & bs[F])
                cl.append(-enc.ge(enc.count(('pair', min(F, L), max(F, L)), [pr(F, L, a) for a in range(61)], max(6, c)), c))
            elif k == 'R3B':
                L = key[2]; cl += neq_set(L, bs[L] & Ns, Ns)
                cl.append(-enc.ge(enc.count(('cnt', L, Pk), [bv(L, a) for a in range(61) if Pk >> a & 1], 6), 6))
            elif k == 'R3P':
                m = key[2]
                cl.append(-enc.ge(enc.count(('cnt', F, base[m]), [bv(F, a) for a in range(61) if base[m] >> a & 1], 6), 6))
            elif k == 'D1B':
                m = key[2]; Pm = base[m]; c0 = bc(Pm & Pk); c = bc(Pm & (Pk | bs[F])) - c0
                reg = Pm & ~Pk
                if c >= 1: cl.append(-enc.ge(enc.count(('cnt', F, reg), [bv(F, a) for a in range(61) if reg >> a & 1], c), c))
            else:   # SA, W7F, W7P
                L, M = key[2], key[3]
                cl += neq_set(L, bs[L] & Ns, Ns) + neq_set(M, bs[M] & Ns, Ns)
                if k == 'SA':
                    c = bc(bs[L] & bs[M] & ~(Pk | bs[F]))
                    if c >= 1:
                        lits = [enc.AND((bv(L, a), bv(M, a), -bv(F, a))) for a in range(61) if not Pk >> a & 1]
                        cl.append(-enc.ge(enc.count(('sa', kk, F, L, M), lits, c), c))
                elif k == 'W7F':
                    c = bc(bs[L] & bs[M] & bs[F] & ~Pk)
                    lits = [enc.AND((bv(L, a), bv(M, a), bv(F, a))) for a in range(61) if not Pk >> a & 1]
                    cl.append(enc.ge(enc.count(('w7f', kk, F, L, M), lits, c + 1), c + 1))
                else:
                    c = bc(bs[L] & bs[M] & Pk & ~bs[F])
                    lits = [enc.AND((bv(L, a), bv(M, a), -bv(F, a))) for a in range(61) if Pk >> a & 1]
                    cl.append(enc.ge(enc.count(('w7p', kk, F, L, M), lits, c + 1), c + 1))
    for F in sorted(cert['kap']):
        cl.append(-enc.ge(enc.count(('size', F), list(bvars[F]), 22), bc(bs[F])))
    return sorted(set(l for l in cl if l != enc.F))


# ------------------------------------------------------------------------------------------------ generic GD1 (trace-free)
# For a slot F with |b_F & P_k| = 5 (a 5-pair (P_k,F), N = P_k & b_F) and another slot L with N not<= b_L:
#   D1 at (P_k,F):  |b_L & (P_k u b_F)| + |L & F & U| <= 9;   Lemma A: |L & F & U| >= 5 - |b_L & b_F|.
#   GD1b:  |b_L & (P_k u b_F)| <= 9                     (from D1 alone, |L&F&U| >= 0)
#   GD1a:  |b_L & P_k \ b_F| <= 4                       (D1 + Lemma A; needs |b_L & b_F| <= 5 ... in general:
#          |b_L & P_k \ b_F| + max(5, |b_L & b_F|) <= 9, whose two halves are GD1a and GD1b)
# Guard: |b_F & P_k| >= 6  OR  (P_k & b_F) <= b_L.   (|b_F & P_k| >= 5 always holds by Lemma A, so '!= 5' is '>= 6'.)
def gd1_instances(b, base, n):
    out = []
    for k in range(4):
        Pk = base[k]
        for F in range(n):
            N = b[F] & Pk
            if bc(N) != 5: continue
            for L in range(n):
                if L == F or not (N & ~b[L]): continue
                if bc(b[L] & Pk & ~b[F]) > 4: out.append(('GD1a', k, F, L))
                elif bc(b[L] & (Pk | b[F])) > 9: out.append(('GD1b', k, F, L))
    return out

def encode_gd1(enc, inst, bvars, base):
    kind, k, F, L = inst; Pk = base[k]; P = [a for a in range(61) if Pk >> a & 1]
    bv = lambda X, a: bvars[X][a]
    cl = [enc.ge(enc.count(('cnt', F, Pk), [bv(F, a) for a in P], 6), 6)]                 # |b_F & P_k| >= 6
    cl.append(enc.AND(tuple(enc.OR((-bv(F, a), bv(L, a))) for a in P)))                   # P_k & b_F <= b_L
    if kind == 'GD1a':
        lits = [enc.AND((bv(L, a), -bv(F, a))) for a in P]
        cl.append(-enc.ge(enc.count(('gd1a', k, F, L), lits, 5), 5))                       # |b_L & P_k \ b_F| <= 4
    else:
        lits = [bv(L, a) if Pk >> a & 1 else enc.AND((bv(L, a), bv(F, a))) for a in range(61)]
        cl.append(-enc.ge(enc.count(('d1', k, F, L), lits, 10), 10))                       # |b_L & (P_k u b_F)| <= 9
    return sorted(set(l for l in cl if l != enc.F))
