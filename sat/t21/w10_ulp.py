r"""Wave 10: exact U-REALIZABILITY LP for a fixed core solution (column generation).
python3 w10_ulp.py STALL.json [maxN=3] [maxN1=4] [nof1]
Given the named (base) traces b_F of the new edges, ask whether outside points (U = points outside the 4 base edges)
can be distributed.  A U-point is described by the set S of modelled new edges containing it; n_S >= 0 = number of
such points.  All constraints are LINEAR in n and are instances of proved facts:
  cap_F : sum_{S ni F} n_S <= 21 - |b_F|                       (|F| = 21)
  A_FG  : sum_{S >= {F,G}} n_S >= 5 - |b_F & b_G|               (Lemma A)
  F1_FGH: b_F&b_G&b_H = {}  =>  sum_{S >= {F,G,H}} n_S >= 1     (F1: three edges with no common point have union <= 48)
  L_fam : fam = B' u N' (B' nonempty set of base edges, N' new), common named intersection empty (base edges contain
          no U-point, so the full intersection is empty)  =>  sum_{S meets N'} n_S >= 61 - |cup B' u cup b_N'|  (L)
Dropping constraints only enlarges the feasible set, so LP-infeasible  =>  this core solution has NO literal
realization (for any number of further points).  The Farkas dual is printed: it is a counting argument.
Phase I: minimise total artificial slack; columns S priced exactly by SCIP (binary MIP)."""
import sys, json, itertools, time
sys.path.insert(0, '../pylib')
from ortools.linear_solver import pywraplp
d = json.load(open(sys.argv[1]))
opt = dict(a.split('=') for a in sys.argv[2:] if '=' in a); flags = [a for a in sys.argv[2:] if '=' not in a]
maxN = int(opt.get('maxN', 3)); maxN1 = int(opt.get('maxN1', 4))
base = [frozenset(b) for b in d['base']]
new = [frozenset(e['pts']) for e in d['edges']]
lab = [e['label'] for e in d['edges']]
n = len(new); NB = len(base)
cap = [21 - len(b) for b in new]
rows = []   # (kind, key, rhs, members) ; kind A: pair, T: triple, L: set N' (column hits if S&N' nonempty)
for F, G in itertools.combinations(range(n), 2):
    r = 5 - len(new[F] & new[G])
    if r > 0: rows.append(('A', (F, G), r))
if 'nof1' not in flags:
    for t in itertools.combinations(range(n), 3):
        if not (new[t[0]] & new[t[1]] & new[t[2]]): rows.append(('T', t, 1))
nL = 0
for kb in range(1, NB + 1):
    for Bp in itertools.combinations(range(NB), kb):
        capB = frozenset.intersection(*[base[i] for i in Bp]); cupB = frozenset.union(*[base[i] for i in Bp])
        mx = maxN1 if kb == 1 else maxN
        for kn in range(1, mx + 1):
            for Np in itertools.combinations(range(n), kn):
                I = capB
                for F in Np: I = I & new[F]
                if I: continue
                U = cupB
                for F in Np: U = U | new[F]
                r = 61 - len(U)
                if r <= 0: continue
                # redundancy: the singleton-in-N' rows with r <= cap are implied by cap? no (cap is <=); keep all
                rows.append(('L', (Bp, Np), r)); nL += 1
print(f'{sys.argv[1]}: new edges {n}, rows A={sum(1 for r in rows if r[0]=="A")} T={sum(1 for r in rows if r[0]=="T")} L={nL}', flush=True)
# quick necessary checks
bad = [(lab[F], cap[F]) for F in range(n) if cap[F] < 0]
if bad: print('oversize named part', bad)
lp = pywraplp.Solver.CreateSolver('GLOP')
art = [lp.NumVar(0, lp.infinity(), f'a{i}') for i in range(len(rows))]
cons = []
for i, (k, key, r) in enumerate(rows):
    c = lp.Constraint(r, lp.infinity()); c.SetCoefficient(art[i], 1); cons.append(c)
capc = [lp.Constraint(-lp.infinity(), cap[F]) for F in range(n)]
lp.Minimize(sum(art))
def hits(k, key, S):
    if k == 'A': return key[0] in S and key[1] in S
    if k == 'T': return all(x in S for x in key)
    return any(x in S for x in key[1])
cols = {}
def addcol(S):
    S = frozenset(S)
    if S in cols: return False
    v = lp.NumVar(0, lp.infinity(), 'n' + '_'.join(map(str, sorted(S)))); cols[S] = v
    for F in S: capc[F].SetCoefficient(v, 1)
    for i, (k, key, r) in enumerate(rows):
        if hits(k, key, S): cons[i].SetCoefficient(v, 1)
    return True
for F in range(n): addcol([F])
for k, key, r in rows:
    if k == 'A': addcol(key)
    if k == 'T': addcol(key)
T0 = time.time(); PSHIFT = 0.0
for it in range(400):
    st = lp.Solve(); val = lp.Objective().Value()
    y = [c.dual_value() for c in cons]; yc = [c.dual_value() for c in capc]
    # pricing: maximise sum_r y_r [hit] + sum_F yc_F x_F   (yc <= 0)
    mip = pywraplp.Solver.CreateSolver('SCIP')
    x = [mip.BoolVar(f'x{F}') for F in range(n)]
    obj = [yc[F] * x[F] for F in range(n)]
    for i, (k, key, r) in enumerate(rows):
        if y[i] <= 1e-9: continue
        z = mip.NumVar(0, 1, '')
        if k == 'A' or k == 'T':
            for a in key: mip.Add(z <= x[a])
        else:
            mip.Add(z <= sum(x[a] for a in key[1]))
        obj.append(y[i] * z)
    mip.Maximize(sum(obj)); mip.Solve(); best = mip.Objective().Value()
    S = [F for F in range(n) if x[F].solution_value() > 0.5]
    LB = val - max(best, 0) * sum(max(c, 0) for c in cap)
    print(f'it {it}: phaseI={val:.4f} cols={len(cols)} price={best:.4f} LB={LB:.3f} |S|={len(S)} ({time.time()-T0:.0f}s)', flush=True)
    if LB > float(opt.get('stopLB', 1e9)): PSHIFT = best; break
    if best <= 1e-7 or not addcol(S):
        break
print('RESULT', 'INFEASIBLE (no literal realization of this core)' if (val > 1e-6 and (PSHIFT>0 or best<=1e-7)) else 'FEASIBLE (LP)', f'phaseI={val:.4f}')
# report dual certificate (positive weights)
y = [c.dual_value() for c in cons]; yc = [c.dual_value() - PSHIFT for c in capc]
print('certificate: sum y*r =', round(sum(yy*r for yy,(k,key,r) in zip(y,rows)),4), ' sum kappa*cap =', round(-sum(yc[F]*cap[F] for F in range(n)),4), ' shift', PSHIFT)
out = dict(phaseI=val, rows=[[k, [list(key[0]), list(key[1])] if k == 'L' else list(key), r, y[i]] for i, (k, key, r) in enumerate(rows) if abs(y[i]) > 1e-9],
           cap=[[lab[F], cap[F], yc[F]] for F in range(n) if abs(yc[F]) > 1e-9],
           cols=[[sorted(S), v.solution_value()] for S, v in cols.items() if v.solution_value() > 1e-9])
json.dump(out, open(sys.argv[1].replace('.json', '_ulp.json'), 'w'))
from collections import Counter
print('dual weight by kind:', Counter({k: round(sum(yy for (kk, _, _), yy in zip(rows, y) if kk == k), 3) for k in 'ATL'}))
print('positive-dual rows:', sum(1 for v in y if v > 1e-9), ' cap duals sum*cap:', round(sum(yc[F]*cap[F] for F in range(n)), 3))
sz = Counter(len(S) for S, v in cols.items() if v.solution_value() > 1e-9); print('support column sizes', dict(sz))
