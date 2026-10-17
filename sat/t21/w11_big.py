r"""Wave 11: LARGE-subset sub-problem for the Benders loop (fallback when no subset of size <= 4 is LP-infeasible).
Same LP and same certificate format as w11_benders (columns: no two slots of one base pair; rows cap / A / T / L), but
over ALL slots E at once, with L rows generated lazily (separation by enumeration of N' subset E per base set B').
If infeasible: exact rational Farkas certificate (same repair as w11_benders.exact_cert) on the generated rows, then a
deletion filter on E (each step re-solved from scratch) -> an irreducible infeasible slot set and its certificate.
Every certificate produced is re-checked exactly by w11b_recheck.check before use (caller)."""
import itertools, time
from fractions import Fraction
import numpy as np
FULL = (1 << 61) - 1

def all_cols(E, pair):
    by = {}
    for F in E: by.setdefault(tuple(pair[F]), []).append(F)
    groups = [[None] + v for v in by.values()]
    cols = []
    for choice in itertools.product(*groups):
        S = tuple(sorted(x for x in choice if x is not None))
        if S: cols.append(S)
    return cols

def base_sets(base):
    out = []
    for kb in range(1, 5):
        for Bp in itertools.combinations(range(4), kb):
            capB = FULL; cupB = 0
            for i in Bp: capB &= base[i]; cupB |= base[i]
            out.append((Bp, capB, cupB))
    return out

def fixed_rows(E, b):
    rows = []
    for F, G in itertools.combinations(E, 2):
        r = 5 - (b[F] & b[G]).bit_count()
        if r > 0: rows.append(('A', (F, G), r))
    for t in itertools.combinations(E, 3):
        if not (b[t[0]] & b[t[1]] & b[t[2]]): rows.append(('T', t, 1))
    return rows

def hits(k, key, S):
    if k in ('A', 'T'): return all(x in S for x in key)
    return any(x in S for x in key[1])

def solve_primal(E, b, base, pair, rows, cols):
    from ortools.linear_solver import pywraplp
    lp = pywraplp.Solver.CreateSolver('GLOP')
    n = [lp.NumVar(0, lp.infinity(), '') for _ in cols]
    for F in E:
        c = lp.Constraint(-lp.infinity(), 21 - b[F].bit_count())
        for j, S in enumerate(cols):
            if F in S: c.SetCoefficient(n[j], 1)
    for k, key, r in rows:
        c = lp.Constraint(r, lp.infinity())
        for j, S in enumerate(cols):
            if hits(k, key, S): c.SetCoefficient(n[j], 1)
    st = lp.Solve()
    if st == pywraplp.Solver.OPTIMAL: return [v.solution_value() for v in n]
    return None

def separate(E, b, base, nval, cols, maxadd=200):
    """most violated L rows (B', N') for the primal point nval."""
    m = len(E); idx = {F: i for i, F in enumerate(E)}
    colmask = np.array([sum(1 << idx[F] for F in S) for S in cols], dtype=np.int64)
    nv = np.array(nval)
    masks = np.arange(1, 1 << m, dtype=np.int64)
    # covered(N') = sum of n_S with S meeting N'
    cov = np.zeros(len(masks))
    for cm, v in zip(colmask, nv):
        if v > 1e-12: cov += v * ((masks & cm) != 0)
    # named intersection / union of b_N' for every N' (iteratively by lowest bit)
    inter = [0] * (1 << m); union = [0] * (1 << m); inter[0] = FULL
    for M in range(1, 1 << m):
        lo = (M & -M).bit_length() - 1; R = M & (M - 1)
        inter[M] = inter[R] & b[E[lo]]; union[M] = union[R] | b[E[lo]]
    out = []
    for Bp, capB, cupB in base_sets(base):
        for M in range(1, 1 << m):
            if inter[M] & capB: continue
            r = 61 - (cupB | union[M]).bit_count()
            if r <= 0: continue
            viol = r - cov[M - 1]
            if viol > 1e-7: out.append((viol, ('L', (Bp, tuple(E[i] for i in range(m) if M >> i & 1)), r)))
    out.sort(key=lambda t: -t[0])
    return [x[1] for x in out[:maxadd]]

def dual_cert(E, b, pair, rows, cols):
    from ortools.linear_solver import pywraplp
    cap = {F: 21 - b[F].bit_count() for F in E}
    lp = pywraplp.Solver.CreateSolver('GLOP')
    y = [lp.NumVar(0, 1, '') for _ in rows]; kap = {F: lp.NumVar(0, lp.infinity(), '') for F in E}
    H = [[i for i, (k, key, r) in enumerate(rows) if hits(k, key, S)] for S in cols]
    for S, h in zip(cols, H):
        c = lp.Constraint(-lp.infinity(), 0)
        for i in h: c.SetCoefficient(y[i], 1)
        for F in S: c.SetCoefficient(kap[F], -1)
    obj = lp.Objective()
    for i, (k, key, r) in enumerate(rows): obj.SetCoefficient(y[i], r)
    for F in E: obj.SetCoefficient(kap[F], -cap[F])
    obj.SetMaximization(); lp.Solve()
    if obj.Value() <= 1e-6: return None
    for den in (1000, 100000):
        Y = [Fraction(v.solution_value()).limit_denominator(den) if v.solution_value() > 1e-9 else Fraction(0) for v in y]
        K = {F: Fraction(kap[F].solution_value()).limit_denominator(den) if kap[F].solution_value() > 1e-9 else Fraction(0) for F in E}
        for _ in range(4):
            bad = 0
            for S, h in zip(cols, H):
                d = sum(Y[i] for i in h) - sum(K[F] for F in S)
                if d > 0:
                    bad += 1
                    for F in S: K[F] += d / len(S)
            if not bad: break
        gap = sum(Y[i] * r for i, (k, key, r) in enumerate(rows)) - sum(K[F] * cap[F] for F in E)
        ok = all(sum(Y[i] for i in h) <= sum(K[F] for F in S) for S, h in zip(cols, H))
        if ok and gap > 0:
            sup = [(k, key, r, Y[i]) for i, (k, key, r) in enumerate(rows) if Y[i] > 0]
            Es = sorted(set(x for k, key, r, yv in sup for x in (key if k != 'L' else key[1])) | {F for F in E if K[F] > 0})
            return dict(E=Es, rows=sup, kap={F: K[F] for F in E if K[F] > 0}, gap=gap)
    return 'numerr'

def infeasible(E, b, base, pair, log=None, maxit=60):
    """None if the LP over slot set E is feasible (with ALL L rows), else an exact certificate (dict) or 'numerr'."""
    E = list(E); cols = all_cols(E, pair); rows = fixed_rows(E, b)
    for it in range(maxit):
        nval = solve_primal(E, b, base, pair, rows, cols)
        if nval is None: return dual_cert(E, b, pair, rows, cols)
        new = separate(E, b, base, nval, cols)
        if not new: return None
        rows += new
    return 'maxit'

def minimal(E, b, base, pair, log=print):
    t = time.time(); c = infeasible(E, b, base, pair)
    if not isinstance(c, dict): return c
    cur = list(c['E'])
    for F in list(cur):
        if F not in cur: continue
        trial = [x for x in cur if x != F]
        c2 = infeasible(trial, b, base, pair)
        if isinstance(c2, dict): c = c2; cur = [x for x in trial if x in c2['E']] if set(c2['E']) <= set(trial) else trial
    c = infeasible(cur, b, base, pair)
    log(f'  big: irreducible infeasible set of size {len(cur)} ({time.time()-t:.0f}s)')
    return c
