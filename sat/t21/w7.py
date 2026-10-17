"""Wave 7 probe model: w6fast.build + extra fixed constraints over all k edges.
fixed: list of (inc, exc, op, val): sum of region counts c[T] with T&inc==inc, T&exc==0 (op val)."""
import sys, time
sys.path.append("work/e616/pylib")
sys.path.append("work/e616/t21")
from ortools.sat.python import cp_model
import w6fast
from w6model import B, show, min_cover
R, K = 21, 5
basesz = {B(0): 9, B(0,1): 3, B(0,2): 3, B(0,3): 3, B(0,1,2): 1, B(0,1,3): 1, B(0,2,3): 1, B(1,2,3): 4,
          B(1): 12, B(2): 12, B(3): 12, 0: 0, B(1,2): 0, B(1,3): 0, B(2,3): 0, B(0,1,2,3): 0}
basesz = {b: s for b, s in basesz.items() if s or b == 0}
x12, x13, x23, C0 = (B(0,1,2), B(3)), (B(0,1,3), B(2)), (B(0,2,3), B(1)), (B(1,2,3), B(0))
Q1, Q2, Q3, Qs = (B(0,1), B(2,3)), (B(0,2), B(1,3)), (B(0,3), B(1,2)), (B(0), B(1,2,3))
O1, O2, O3 = (B(1), B(0,2,3)), (B(2), B(0,1,3)), (B(3), B(0,1,2))
def solve(k, pats, fixed, tl=100, workers=2, maxfam=99):
    t0 = time.time()
    m, c, regs = w6fast.build(k, 4, basesz, pats, r=R, K=K, W=60, maxfam=maxfam)
    for inc, exc, op, val in fixed:
        s = sum(c[T] for T in regs if (T & inc) == inc and (T & exc) == 0)
        if op == '==': m.Add(s == val)
        elif op == '>=': m.Add(s >= val)
        else: m.Add(s <= val)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m); name = s.StatusName(st)
    sol = {T: s.Value(c[T]) for T in regs if s.Value(c[T])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return name, sol, time.time() - t0
def cegar(pats, fixed, kmax, tl, label=''):
    k = 4 + len(pats)
    while True:
        st, sol, t = solve(k, pats, fixed, tl)
        print(f'{label} k={k} {st} {t:.1f}s', flush=True)
        if sol is None: return st
        if k >= kmax: print('  sol:', show(k, sol), flush=True); return st
        cov = min_cover(k, sol)
        if cov is None: print('  TAU>=5 sol', show(k, sol)); return 'TAU'
        full = (1 << k) - 1; pats[k] = [(T, full ^ T, mu) for T, mu in cov]
        print('  cover ->', [(bin(T)[2:].zfill(k)[::-1], mu) for T, mu in cov], flush=True); k += 1
