r"""Wave 11: try to turn a Benders STALL (named traces b, whole-set LP feasible) into a LITERAL partial hypergraph.
  python3 w11_realize.py TAG [tlim]     reads w11s_TAG_meta.json + w11s_TAG_stall.json
Integer n_S (points outside P0..P3 lying in exactly the slots S; S(a): no two slots of one base pair) with
|F| = 21 exactly, Lemma A; then a lazy loop: build the hypergraph literally, find EVERY subfamily with union <= 60 and
empty intersection (exact DFS, base + new edges), add its L constraint (disjunction: common outside point OR union >= 61),
and also forbid accidental 5-pairs among new edges that violate R3/SA/D1/W7/TT (heuristic search restriction, not a lemma).
Output w11s_TAG_real.json (edges + labels) for the independent checker w10x_verify.py.  This is SEARCH, not proof."""
import sys, os, json, itertools, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
from ortools.sat.python import cp_model
tag = sys.argv[1]; tlim = float(sys.argv[2]) if len(sys.argv) > 2 else 600
meta = json.load(open(os.path.join(HERE, f'w11s_{tag}_meta.json')))
st = json.load(open(os.path.join(HERE, sys.argv[3] if len(sys.argv) > 3 else f'w11s_{tag}_stall.json')))
names = meta['names']; P = [frozenset(p) for p in meta['P']]; slots = meta['slots']; n = len(slots)
pair = [tuple(s['pair']) for s in slots]; b = [frozenset(a for a in range(61) if st['b'][F] >> a & 1) for F in range(n)]
labels = [f'P{k}' for k in range(4)] + [f"{pair[F]}:{slots[F]['x']}" for F in range(n)]
by = {}
for F in range(n): by.setdefault(pair[F], []).append(F)
cols = []
for ch in itertools.product(*[[None] + v for v in by.values()]):
    S = tuple(sorted(x for x in ch if x is not None))
    if S: cols.append(S)
m = cp_model.CpModel()
x = {S: m.NewIntVar(0, 21, '') for S in cols}
for F in range(n): m.Add(len(b[F]) + sum(x[S] for S in cols if F in S) == 21)
for F, G in itertools.combinations(range(n), 2):
    m.Add(len(b[F] & b[G]) + sum(x[S] for S in cols if F in S and G in S) >= 5)
nfam = 0; forb = set()
def add_L(Bp, Np):
    global nfam
    I = frozenset(range(61))
    for k in Bp: I &= P[k]
    for F in Np: I &= b[F]
    if I: return
    U = frozenset().union(*[P[k] for k in Bp], *[b[F] for F in Np])
    need = 61 - len(U)
    if need <= 0: return
    cov = sum(x[S] for S in cols if any(F in S for F in Np))
    if Bp:
        m.Add(cov >= need)
    else:
        z = m.NewBoolVar('')
        m.Add(sum(x[S] for S in cols if all(F in S for F in Np)) >= 1).OnlyEnforceIf(z)
        m.Add(cov >= need).OnlyEnforceIf(z.Not())
    nfam += 1
def build(sol):
    pid = 61; E = [set(p) for p in P] + [set(bf) for bf in b]
    for S in cols:
        for _ in range(sol[S]):
            for F in S: E[4 + F].add(pid)
            pid += 1
    return [frozenset(e) for e in E]
def violations(E):
    N = len(E); bad = []
    def dfs(start, U, I, fam):
        if len(fam) >= 2 and not I: bad.append(tuple(fam)); return
        for k in range(start, N):
            U2 = U | E[k]
            if len(U2) > 60: continue
            dfs(k + 1, U2, (I & E[k]) if fam else E[k], fam + [k])
    dfs(0, frozenset(), frozenset(), [])
    return bad
def five_pair_viol(E):
    """accidental/derived 5-pairs: R3 / SA / D1 / W7 / TT-like checks as in w10x_verify (returns offending pairs)."""
    out = set(); N = len(E)
    for i, j in itertools.combinations(range(N), 2):
        Nn = E[i] & E[j]
        if len(Nn) != 5: continue
        U = E[i] | E[j]; sing = {}
        for k in range(N):
            if k in (i, j): continue
            t = E[k] & Nn
            if len(t) == 1: sing.setdefault(next(iter(t)), []).append(k)
            if not Nn <= E[k] and len(E[k] & U) > 9: out.add((i, j, 'D1', k))
        for t, ks in sing.items():
            for k in ks:
                if len(E[k] & E[i]) != 5 or len(E[k] & E[j]) != 5: out.add((i, j, 'R3', k))
        for t1, t2 in itertools.combinations(sing, 2):
            for a in sing[t1]:
                for c in sing[t2]:
                    AB = E[a] & E[c]
                    if AB - U: out.add((i, j, 'SA', a, c))
                    if len(AB & (E[i] - E[j])) < 2 or len(AB & (E[j] - E[i])) < 2: out.add((i, j, 'W7', a, c))
    return out
NOFV = "nofv" in sys.argv
T0 = time.time(); it = 0
while time.time() - T0 < tlim:
    sv = cp_model.CpSolver(); sv.parameters.max_time_in_seconds = max(10, tlim - (time.time() - T0)); sv.parameters.num_workers = 1
    r = sv.Solve(m)
    if r not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        print(f'it {it}: integer model {sv.StatusName(r)} after {nfam} L families, {len(forb)} forbidden 5-pairs'); break
    sol = {S: sv.Value(x[S]) for S in cols}; E = build(sol)
    bad = violations(E); fv = five_pair_viol(E)
    print(f'it {it}: {len(bad)} L violations, {len(fv)} 5-pair-lemma violations ({time.time()-T0:.0f}s)', flush=True)
    from collections import Counter; print("   ", Counter((v[2], v[0] < 4 and v[1] < 4) for v in fv), [(labels[v[0]], labels[v[1]], v[2]) for v in list(fv)[:6]], flush=True)
    if not bad and not fv:
        json.dump(dict(edges=[sorted(e) for e in E], labels=labels, named=names), open(os.path.join(HERE, f'w11_{tag}_real.json'), 'w'))
        print('REALIZED: wrote', f'w11_{tag}_real.json'); break
    for fam in bad: add_L([k for k in fam if k < 4], [k - 4 for k in fam if k >= 4])
    if NOFV and fv and not bad:   # search exclusion: some column through a violating new-new pair must change
        diffs = []
        for v in fv:
            i, j = v[0], v[1]
            for S in cols:
                if (i < 4 or i - 4 in S) and (j < 4 or j - 4 in S):
                    d = m.NewBoolVar(''); m.Add(x[S] != sol[S]).OnlyEnforceIf(d); m.Add(x[S] == sol[S]).OnlyEnforceIf(d.Not()); diffs.append(d)
        m.AddBoolOr(diffs)
    for v in ([] if NOFV else fv):   # forbid this accidental 5-pair among new edges (search restriction): |F&G| != 5
        i, j = v[0], v[1]
        if i >= 4 and j >= 4 and (i, j) not in forb:
            F, G = i - 4, j - 4; forb.add((i, j))
            m.Add(len(b[F] & b[G]) + sum(x[S] for S in cols if F in S and G in S) >= 6)
    it += 1
