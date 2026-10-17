r"""Wave 10: minimal infeasible sub-configurations of the U-realizability LP (w10_ulp.py rows), deletion filter.
python3 w10_iis.py STALL.json [maxN=3] [maxN1=4]
For a subset E of the new edges, rows are the w10_ulp rows restricted to E (A, F1-triples, L with B' nonempty).
Small |E| (<= 12): all 2^|E|-1 columns enumerated (exact LP).  Otherwise column generation with exact SCIP pricing and
the Lagrangian lower bound (phaseI - price * sum cap) for early infeasibility.  Output: a minimal (w.r.t. deletion)
set of new edges whose base traces admit no realization of the outside points."""
import sys, json, itertools, time
sys.path.insert(0, '../pylib')
from ortools.linear_solver import pywraplp
d = json.load(open(sys.argv[1]))
opt = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
maxN = int(opt.get('maxN', 3)); maxN1 = int(opt.get('maxN1', 4))
base = [frozenset(b) for b in d['base']]; NB = len(base)
new = [frozenset(e['pts']) for e in d['edges']]; lab = [e['label'] for e in d['edges']]
cap = [21 - len(b) for b in new]
def rows_for(E):
    rows = []
    for F, G in itertools.combinations(E, 2):
        r = 5 - len(new[F] & new[G])
        if r > 0: rows.append(('A', (F, G), r))
    for t in itertools.combinations(E, 3):
        if not (new[t[0]] & new[t[1]] & new[t[2]]): rows.append(('T', t, 1))
    for kb in range(1, NB + 1):
        for Bp in itertools.combinations(range(NB), kb):
            capB = frozenset.intersection(*[base[i] for i in Bp]); cupB = frozenset.union(*[base[i] for i in Bp])
            for kn in range(1, (maxN1 if kb == 1 else maxN) + 1):
                for Np in itertools.combinations(E, kn):
                    I = capB; U = cupB
                    for F in Np: I = I & new[F]; U = U | new[F]
                    if I: continue
                    if 61 - len(U) > 0: rows.append(('L', (Bp, Np), 61 - len(U)))
    return rows
def hits(k, key, S):
    if k == 'A': return key[0] in S and key[1] in S
    if k == 'T': return all(x in S for x in key)
    return any(x in S for x in key[1])
def infeasible(E, verbose=False, ret=False):
    E = list(E); rows = rows_for(E)
    lp = pywraplp.Solver.CreateSolver('GLOP')
    art = [lp.NumVar(0, lp.infinity(), '') for _ in rows]
    cons = []
    for i, (k, key, r) in enumerate(rows):
        c = lp.Constraint(r, lp.infinity()); c.SetCoefficient(art[i], 1); cons.append(c)
    capc = {F: lp.Constraint(-lp.infinity(), cap[F]) for F in E}
    lp.Minimize(sum(art)); cols = {}
    def addcol(S):
        S = frozenset(S)
        if S in cols: return False
        v = lp.NumVar(0, lp.infinity(), ''); cols[S] = v
        for F in S: capc[F].SetCoefficient(v, 1)
        for i, (k, key, r) in enumerate(rows):
            if hits(k, key, S): cons[i].SetCoefficient(v, 1)
        return True
    if len(E) <= 12:
        for m in range(1, len(E) + 1):
            for S in itertools.combinations(E, m): addcol(S)
        lp.Solve(); val = lp.Objective().Value()
        res = val > 1e-6
    else:
        for F in E: addcol([F])
        for k, key, r in rows:
            if k in 'AT': addcol(key)
        res = None
        for it in range(1000):
            lp.Solve(); val = lp.Objective().Value()
            if val <= 1e-7: res = False; break
            y = [c.dual_value() for c in cons]
            mip = pywraplp.Solver.CreateSolver('SCIP'); x = {F: mip.BoolVar('') for F in E}
            obj = [capc[F].dual_value() * x[F] for F in E]
            for i, (k, key, r) in enumerate(rows):
                if y[i] <= 1e-9: continue
                z = mip.NumVar(0, 1, '')
                if k in 'AT':
                    for a in key: mip.Add(z <= x[a])
                else: mip.Add(z <= sum(x[a] for a in key[1]))
                obj.append(y[i] * z)
            mip.Maximize(sum(obj)); mip.Solve(); best = mip.Objective().Value()
            if val - max(best, 0) * sum(cap[F] for F in E) > 0.5: res = True; break
            if best <= 1e-7: res = val > 1e-6; break
            addcol([F for F in E if x[F].solution_value() > 0.5])
    if ret: return res, rows, cons, capc, cols, lp
    return res
if __name__ == '__main__':
    E = list(range(len(new))); T0 = time.time()
    assert infeasible(E), 'full set feasible'
    print('full set infeasible', flush=True)
    i = 0
    order = sorted(E, key=lambda F: cap[F])   # try removing small-outside edges first? keep simple
    for F in list(order):
        trial = [x for x in E if x != F]
        if infeasible(trial): E = trial; print(f'  drop {lab[F]} -> {len(E)} left ({time.time()-T0:.0f}s)', flush=True)
        else: print(f'  keep {lab[F]} ({time.time()-T0:.0f}s)', flush=True)
    print('MINIMAL', len(E), [lab[F] for F in E])
    json.dump(dict(src=sys.argv[1], minimal=E, labels=[lab[F] for F in E]), open(sys.argv[1].replace('.json', f'_iis_{maxN}{maxN1}.json'), 'w'))
