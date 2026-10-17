r"""Wave 11 N-K4: Benders loop  (master = named-trace CNF, sub = exact outside-point LP with S(a)).
Usage:  python3 w11_benders.py prep            -> builds w8sat master ('3211', all 24 gen-1 singles, +TT, +SB),
                                                 writes w11_base.cnf + w11_meta.json
        python3 w11_benders.py run TLIM [maxk=4] -> Benders iterations until UNSAT / stall / time limit; checkpointed
                                                 (w11_cuts.cnf, w11_state.json, w11_certs/c*.json, w11.log)
MASTER: w8sat.build (sound, see Wave 8 NK4.3): traces b_F over the 61 named points of P0..P3 for the 24 singles.
SUB (for a subset E of new edges, traces fixed): variables n_S >= 0 = number of points outside P0u..uP3 lying in
exactly the slots S (S subset of E).  Allowed columns: S contains no two singles of the same base pair (S(a)/R.3:
cross-type singles of a 5-pair have disjoint parts outside X u Y; in the (3,2,1,1)-K4 every base pair has one single
per type, so all singles of one pair are cross-type).  Rows (all instances of proved facts, as in w10_ulp.py):
  cap_F : sum_{S ni F} n_S <= 21 - |b_F|
  A_FG  : sum_{S >= {F,G}} n_S >= 5 - |b_F & b_G|                    (Lemma A)
  T_FGH : b_F&b_G&b_H = {}  =>  sum_{S >= {F,G,H}} n_S >= 1           (F1)
  L_B'N': B' nonempty base set, N' subset E, (cap B') & (cap b_N') = {}  =>  sum_{S meets N'} n_S >= 61 - |cup B' u cup b_N'|
FARKAS: y >= 0 on rows, k >= 0 on caps with  sum_{r hit by S} y_r <= sum_{F in S} k_F  for every allowed column S and
  sum_r y_r rhs_r(b*) > sum_F k_F (21 - |b*_F|).  For ANY traces b the realizable n gives
  sum_r y_r rhs_r(b) <= sum_S n_S sum_{r hit by S} y_r <= sum_F k_F sum_{S ni F} n_S <= sum_F k_F (21-|b_F|)
  (rhs_r(b) := max(0, rhs) if the row's emptiness condition holds, else 0; column/hit structure is independent of b).
CUT (monotone no-good): rhs_r is antitone in |b_F&b_G| (A), in [triple nonempty] (T), in [intersection nonempty] and
  |union| (L); cap is antitone in |b_F|.  So if every supported row has rhs_r(b) >= rhs_r(b*) and every k_F>0 edge has
  |b_F| >= |b*_F|, the inequality is violated  =>  no realization.  Clause = OR of the negated conditions:
  [|b_F&b_G| >= k*+1] | [b_F&b_G&b_H != {}] | [(capB')&(cap b_N') != {}] | [|union| >= u*+1] | [|b_F| <= |b*_F|-1].
  Each literal is an aux variable that IMPLIES its condition (one-directional definitions suffice for soundness:
  a real configuration satisfies the clause by setting the aux of a true condition).
"""
import sys, os, json, itertools, time
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
CERTDIR = os.path.join(HERE, 'w11b_certs')
BSUF = os.environ.get('W11BASE', '')   # '' = w8sat master; '2' = master + eager L4A

def log(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True)
    with open(os.path.join(HERE, 'w11b.log'), 'a') as f: f.write(s + '\n')

# ------------------------------------------------------------------------------------------------- subproblem
def setup(meta):
    names = meta['names']; P = [set(p) for p in meta['P']]
    base = [sum(1 << a for a in P[k]) for k in range(4)]
    return names, base

def allowed_cols(E, pair):
    cols = []
    for m in range(1, len(E) + 1):
        for S in itertools.combinations(E, m):
            ps = [tuple(pair[F]) for F in S]
            if len(set(ps)) == len(ps): cols.append(S)
    return cols

def rows_for(E, b, base, maxNp=None):
    """rows with positive rhs; L rows for every nonempty B' and nonempty N' subset of E (|N'| <= maxNp)."""
    rows = []
    for F, G in itertools.combinations(E, 2):
        r = 5 - (b[F] & b[G]).bit_count()
        if r > 0: rows.append(('A', (F, G), r))
    for t in itertools.combinations(E, 3):
        if not (b[t[0]] & b[t[1]] & b[t[2]]): rows.append(('T', t, 1))
    full = (1 << 61) - 1
    for kb in range(1, 5):
        for Bp in itertools.combinations(range(4), kb):
            capB = full; cupB = 0
            for i in Bp: capB &= base[i]; cupB |= base[i]
            for kn in range(1, (maxNp or len(E)) + 1):
                for Np in itertools.combinations(E, kn):
                    I = capB; U = cupB
                    for F in Np: I &= b[F]; U |= b[F]
                    if I: continue
                    r = 61 - U.bit_count()
                    if r > 0: rows.append(('L', (Bp, Np), r))
    return rows

def hits(k, key, S):
    if k == 'A' or k == 'T': return all(x in S for x in key)
    return any(x in S for x in key[1])

def dual_lp(E, b, base, pair):
    """max sum y r - sum k cap  s.t. column constraints, 0<=y<=1, k>=0.  Returns (value, rows, cols, y, kap)."""
    from ortools.linear_solver import pywraplp
    rows = rows_for(E, b, base); cols = allowed_cols(E, pair)
    cap = {F: 21 - b[F].bit_count() for F in E}
    lp = pywraplp.Solver.CreateSolver('GLOP')
    y = [lp.NumVar(0, 1, '') for _ in rows]; kap = {F: lp.NumVar(0, lp.infinity(), '') for F in E}
    for S in cols:
        c = lp.Constraint(-lp.infinity(), 0)
        for i, (k, key, r) in enumerate(rows):
            if hits(k, key, S): c.SetCoefficient(y[i], 1)
        for F in S: c.SetCoefficient(kap[F], -1)
    obj = lp.Objective()
    for i, (k, key, r) in enumerate(rows): obj.SetCoefficient(y[i], r)
    for F in E: obj.SetCoefficient(kap[F], -cap[F])
    obj.SetMaximization(); lp.Solve()
    return obj.Value(), rows, cols, [v.solution_value() for v in y], {F: kap[F].solution_value() for F in E}

def exact_cert(E, b, base, pair):
    val, rows, cols, y, kap = dual_lp(E, b, base, pair)
    if val <= 1e-6: return None
    Y = [Fraction(v).limit_denominator(1000) if v > 1e-9 else Fraction(0) for v in y]
    K = {F: Fraction(kap[F]).limit_denominator(1000) if kap[F] > 1e-9 else Fraction(0) for F in E}
    # repair: raise kappa so every column constraint holds exactly
    for _ in range(3):
        bad = 0
        for S in cols:
            lhs = sum(Y[i] for i, (k, key, r) in enumerate(rows) if Y[i] and hits(k, key, S))
            d = lhs - sum(K[F] for F in S)
            if d > 0:
                bad += 1
                for F in S: K[F] += d / len(S)
        if not bad: break
    cap = {F: 21 - b[F].bit_count() for F in E}
    gap = sum(Y[i] * r for i, (k, key, r) in enumerate(rows)) - sum(K[F] * cap[F] for F in E)
    ok = all(sum(Y[i] for i, (k, key, r) in enumerate(rows) if Y[i] and hits(k, key, S)) <= sum(K[F] for F in S) for S in cols)
    if not ok or gap <= 0: return 'numerr'
    sup = [(k, key, r, Y[i]) for i, (k, key, r) in enumerate(rows) if Y[i] > 0]
    return dict(E=list(E), rows=sup, kap={F: K[F] for F in E if K[F] > 0}, gap=gap)

# ------------------------------------------------------------------------------------------------- cut encoding
class PEnc:
    """Persistent, cached encoder for cut literals.  All aux definitions are EXACT (both directions), cached by key,
    so a pair count / union count used by many cuts is encoded once.  T = constant-true literal of the base CNF."""
    def __init__(s, top, T): s.top = top; s.T = T; s.F = -T; s.cl = []; s.c = {}
    def new(s): s.top += 1; return s.top
    def AND(s, lits):
        lits = tuple(sorted(set(lits)))
        if len(lits) == 1: return lits[0]
        k = ('and', lits)
        if k not in s.c:
            z = s.new(); s.cl += [[-z, l] for l in lits] + [[z] + [-l for l in lits]]; s.c[k] = z
        return s.c[k]
    def OR(s, lits):
        lits = tuple(sorted(set(lits)))
        if len(lits) == 1: return lits[0]
        k = ('or', lits)
        if k not in s.c:
            z = s.new(); s.cl += [[-z] + list(lits)] + [[z, -l] for l in lits]; s.c[k] = z
        return s.c[k]
    def count(s, key, lits, cap):
        """O with O[m-1] <-> (sum lits >= m), m = 1..min(cap, len); exact totalizer (truncated at cap)."""
        k = ('cnt', key)
        if k in s.c and len(s.c[k]) >= min(cap, len(lits)): return s.c[k]
        if k in s.c: cap = max(cap, len(s.c[k]) + 4)          # grow (a fresh exact totalizer replaces the cached one)
        def tot(ls):
            if len(ls) == 1: return [ls[0]]
            h = len(ls) // 2; A = tot(ls[:h]); B = tot(ls[h:]); n = min(len(A) + len(B), cap)
            O = [s.new() for _ in range(n)]
            for i in range(len(A) + 1):
                for j in range(len(B) + 1):
                    if 1 <= i + j:                                   # A>=i & B>=j -> O>=min(i+j,n)
                        c = [O[min(i + j, n) - 1]]
                        if i: c.append(-A[i - 1])
                        if j: c.append(-B[j - 1])
                        s.cl.append(c)
                    if i + j < n:                                     # O>=i+j+1 -> A>=i+1 or B>=j+1
                        c = [-O[i + j]]
                        if i < len(A): c.append(A[i])
                        if j < len(B): c.append(B[j])
                        s.cl.append(c)
            return O
        s.c[k] = tot(list(lits)); return s.c[k]
    def ge(s, O, m):
        if m <= 0: return s.T
        if m > len(O): return s.F
        return O[m - 1]

def encode_cut(enc, cert, b_star, bvars, base_masks):
    """returns the cut clause; definitions go to enc.cl (exact, cached)."""
    clause = []
    full = (1 << 61) - 1
    pr = lambda F, G, a: enc.AND((bvars[min(F, G)][a], bvars[max(F, G)][a]))
    for (k, key, r, yv) in cert['rows']:
        if k == 'A':
            F, G = sorted(key); ks = (b_star[F] & b_star[G]).bit_count()
            O = enc.count(('pair', F, G), [pr(F, G, a) for a in range(61)], 6)
            clause.append(enc.ge(O, ks + 1))
        elif k == 'T':
            F, G, H = sorted(key)
            clause.append(enc.OR([enc.AND((pr(F, G, a), bvars[H][a])) for a in range(61)]))
        else:
            Bp, Np = key; Np = tuple(sorted(Np)); capB = full; cupB = 0
            for i in Bp: capB &= base_masks[i]; cupB |= base_masks[i]
            Ustar = cupB
            for F in Np: Ustar |= b_star[F]
            inter = [a for a in range(61) if capB >> a & 1]
            if inter: clause.append(enc.OR([enc.AND(tuple(bvars[F][a] for F in Np)) for a in inter]))
            outside = [a for a in range(61) if not (cupB >> a & 1)]
            orl = [enc.OR([bvars[F][a] for F in Np]) for a in outside]
            need = Ustar.bit_count() + 1 - cupB.bit_count()
            O = enc.count(('union', cupB, Np), orl, need)     # truncated at the needed threshold (exact below it)
            clause.append(enc.ge(O, need))
    for F in sorted(cert['kap']):
        O = enc.count(('size', F), list(bvars[F]), 22)
        clause.append(-enc.ge(O, b_star[F].bit_count()))      # |b_F| <= |b*_F| - 1
    clause = sorted(set(l for l in clause if l != enc.F))
    return clause

def cert_to_internal(rec):
    rows = [(k, (tuple(key[0]), tuple(key[1])) if k == 'L' else tuple(key), r, Fraction(y)) for k, key, r, y in rec['rows']]
    b = {int(F): sum(1 << a for a in v) for F, v in rec['traces'].items()}
    return dict(E=rec['E'], rows=rows, kap={int(F): Fraction(v) for F, v in rec['kap'].items()}), b

def rebuild_cuts(meta, bvars, base):
    """deterministically re-encode ALL stored certificates into w11b_cuts.cnf; returns (enc, clauses)."""
    import glob
    files = sorted(glob.glob(os.path.join(CERTDIR, 'c*.json')), key=lambda p: int(os.path.basename(p)[1:-5]))
    enc = PEnc(meta['top'], meta['T']); cuts = []
    for p in files:
        rec = json.load(open(p))
        if rec.get('generic'):
            g = rec['generic']; cuts.append(encode_gen(enc, (g['kind'], tuple(rec['gen_E']), g['mid'], tuple(g['Bp'])), bvars, base)); continue
        c, bs = cert_to_internal(rec)
        bfull = [0] * len(bvars)
        for F, v in bs.items(): bfull[F] = v
        cuts.append(encode_cut(enc, c, bfull, bvars, base))
    with open(os.path.join(HERE, 'w11b_cuts.cnf'), 'w') as f:
        for c_ in enc.cl + cuts: f.write(' '.join(map(str, c_)) + ' 0\n')
    return enc, enc.cl + cuts, len(files)


# ------------------------------------------------------------------------------------------------- generic (trace-free) cuts
# GEN2 (F,G; B'):  guard (capB' & b_F & b_G != {})  OR  |(b_F u b_G) & B| <= |B| - 24          [B = cup B']
# GEN3 (F,G,H; mid G; B'): guard (capB' & b_F&b_G&b_H != {}) OR |(b_F u b_G u b_H) & B| + |(b_F & b_H) \ b_G| <= |B| - 8
# Both are the Farkas combination y = 1 on A_FG (and A_GH), y = 1 on L(B', N'), kappa = 1 on each edge, with the LINEAR
# right-hand sides 5 - |b_F&b_G| (<= max(0, .)) and 61 - |B u cup b| (row valid for any value when the guard fails):
#   GEN2:  (5 - s_FG) + 61 - |B u b_F u b_G| <= 42 - |b_F| - |b_G|            <=>  |(b_F u b_G) & B| <= |B| - 24
#   GEN3:  (5-s_FG)+(5-s_GH)+61-|B u b_F u b_G u b_H| <= 63 - sum|b|          <=>  the GEN3 form above
# (identities re-verified numerically in w11b_recheck.py).  Dual feasibility of (y, kappa) is independent of traces.
def gen_instances(b, base, n, pair):
    full = (1 << 61) - 1; out = []
    Bs = []
    for kb in range(1, 5):
        for Bp in itertools.combinations(range(4), kb):
            capB = full; cupB = 0
            for i in Bp: capB &= base[i]; cupB |= base[i]
            Bs.append((Bp, capB, cupB, cupB.bit_count()))
    for F, G in itertools.combinations(range(n), 2):
        I = b[F] & b[G]; U = b[F] | b[G]
        for Bp, capB, cupB, nB in Bs:
            if I & capB: continue
            if (U & cupB).bit_count() > nB - 24: out.append(('GEN2', (F, G), None, Bp))
    for t in itertools.combinations(range(n), 3):
        I = b[t[0]] & b[t[1]] & b[t[2]]; U = b[t[0]] | b[t[1]] | b[t[2]]
        for mid in t:
            F, H = [x for x in t if x != mid]; G = mid
            FH = (b[F] & b[H] & ~b[G]).bit_count()
            for Bp, capB, cupB, nB in Bs:
                if I & capB: continue
                if (U & cupB).bit_count() + FH > nB - 8: out.append(('GEN3', (F, G, H), G, Bp))
    return out

def gen_cert(inst):
    kind, E, mid, Bp = inst
    if kind == 'GEN2':
        F, G = E; rows = [('A', (F, G), None, Fraction(1)), ('L', (tuple(Bp), (F, G)), None, Fraction(1))]
    else:
        F, G, H = E; rows = [('A', tuple(sorted((F, G))), None, Fraction(1)), ('A', tuple(sorted((G, H))), None, Fraction(1)),
                             ('L', (tuple(Bp), tuple(sorted(E))), None, Fraction(1))]
    return dict(E=sorted(E), rows=rows, kap={x: Fraction(1) for x in E}, generic=dict(kind=kind, mid=mid, Bp=list(Bp)))

def encode_gen(enc, inst, bvars, base_masks):
    kind, E, mid, Bp = inst
    full = (1 << 61) - 1; capB = full; cupB = 0
    for i in Bp: capB &= base_masks[i]; cupB |= base_masks[i]
    Bl = [a for a in range(61) if cupB >> a & 1]; nB = len(Bl)
    Es = tuple(sorted(E))
    guard = [enc.AND(tuple(bvars[x][a] for x in Es)) for a in range(61) if capB >> a & 1]
    lits = [enc.OR([bvars[x][a] for x in Es]) for a in Bl]
    if kind == 'GEN2': bound = nB - 24
    else:
        F, H = [x for x in Es if x != mid]
        lits += [enc.AND((bvars[F][a], bvars[H][a], -bvars[mid][a])) for a in range(61)]
        bound = nB - 8
    O = enc.count(('gen', kind, Es, mid, cupB), lits, bound + 1)
    return sorted(set(guard + [-enc.ge(O, bound + 1)]) - {enc.F})

# ------------------------------------------------------------------------------------------------- driver
def prep():
    from w8sat import build
    from pysat.formula import CNF
    t = time.time(); e, X, pts, W = build('3211', tt=True, sb=True)
    CNF(from_clauses=e.cl).to_file(os.path.join(HERE, 'w11_base.cnf'))
    n = len(pts); P = [[a for a in range(n) if k in pts[a][1]] for k in range(4)]
    meta = dict(names=[p[0] for p in pts], P=P, T=e.T, top=e.pool.top,
                slots=[dict(pair=list(F['pair']), x=pts[F['x']][0], b=F['b']) for F in X], nclauses=len(e.cl))
    json.dump(meta, open(os.path.join(HERE, 'w11_meta.json'), 'w'))
    print('prep done', len(e.cl), e.pool.top, f'{time.time()-t:.0f}s')

def load_cnf(path):
    cl = []
    with open(path) as f:
        for line in f:
            if line[0] in 'pc': continue
            v = list(map(int, line.split()))
            if v: cl.append(v[:-1])
    return cl

def scan(b, base, pair, maxk, n, budget):
    """all minimal infeasible subsets of size <= maxk (sizes in increasing order)."""
    found = []; t0 = time.time()
    for k in range(2, maxk + 1):
        for E in itertools.combinations(range(n), k):
            if any(set(f) <= set(E) for f in found): continue
            c = exact_cert(E, b, base, pair)
            if c == 'numerr': log('  numerr', E); continue
            if c: found.append(E); yield c
            if time.time() - t0 > budget: return
        if found: return   # cuts found at this size: go back to the master

def run(tlim, maxk):
    from pysat.solvers import Cadical153
    meta = json.load(open(os.path.join(HERE, f'w11_meta{BSUF}.json'))); names, base = setup(meta)
    slots = meta['slots']; n = len(slots); pair = [tuple(s_['pair']) for s_ in slots]
    bvars = [s_['b'] for s_ in slots]
    stp = os.path.join(HERE, 'w11b_state.json')
    st = json.load(open(stp)) if os.path.exists(stp) else dict(top=meta['top'], ncuts=0, it=0, history=[])
    os.makedirs(CERTDIR, exist_ok=True)
    T0 = time.time()
    cl = load_cnf(os.path.join(HERE, f'w11_base{BSUF}.cnf')); cutp = os.path.join(HERE, 'w11b_cuts.cnf')
    enc, cc, nc = rebuild_cuts(meta, bvars, base); cl += cc; st['ncuts'] = nc; enc.cl = []; st['top'] = enc.top; log(f'rebuilt {nc} cuts: {len(cc)} clauses')
    log(f'== run start it={st["it"]} cuts={st["ncuts"]} clauses={len(cl)} load {time.time()-T0:.0f}s')
    s = Cadical153(bootstrap_with=cl); del cl
    while time.time() - T0 < tlim:
        t1 = time.time(); r = s.solve(); ts = time.time() - t1
        if not r:
            log(f'it {st["it"]}: MASTER UNSAT ({ts:.1f}s) cuts={st["ncuts"]}'); open(os.path.join(HERE, 'w11b.UNSAT'), 'w').write('UNSAT\n')
            break
        m = set(l for l in s.get_model() if l > 0)
        b = [sum(1 << a for a in range(61) if bvars[F][a] in m) for F in range(n)]
        json.dump(dict(b=b), open(os.path.join(HERE, 'w11b_lastsol.json'), 'w'))
        t2 = time.time(); newc = []
        gi = gen_instances(b, base, n, pair)
        if gi:
            cuts = []
            for inst in gi:
                idx = st['ncuts']; st['ncuts'] += 1; c = gen_cert(inst)
                clause = encode_gen(enc, inst, bvars, base)
                rec = dict(idx=idx, it=st['it'], E=c['E'], gen_E=list(inst[1]), generic=c['generic'],
                           traces={str(F): [a for a in range(61) if b[F] >> a & 1] for F in c['E']},
                           pairs={str(F): list(pair[F]) for F in c['E']},
                           rows=[[k, [list(key[0]), list(key[1])] if k == 'L' else list(key), None, str(yv)] for (k, key, r, yv) in c['rows']],
                           kap={str(F): str(v) for F, v in c['kap'].items()}, cut_clause=clause)
                json.dump(rec, open(os.path.join(CERTDIR, f'c{idx}.json'), 'w')); cuts.append(clause)
            allc = enc.cl + cuts; enc.cl = []; st['top'] = enc.top
            with open(cutp, 'a') as f:
                for c_ in allc: f.write(' '.join(map(str, c_)) + ' 0\n')
            for c_ in allc: s.add_clause(c_)
            from collections import Counter
            kinds = Counter((x[0], len(x[3])) for x in gi)
            st['history'].append([st['it'], ts, 0, len(gi), 'gen'])
            log(f'it {st["it"]}: master SAT ({ts:.1f}s); {len(gi)} GENERIC cuts {dict(kinds)}; total cuts {st["ncuts"]}, aux top {st["top"]}')
            st['it'] += 1; json.dump(st, open(stp, 'w')); continue
        for c in scan(b, base, pair, maxk, n, budget=max(60, tlim - (time.time() - T0))):
            newc.append(c)
        tsc = time.time() - t2
        if not newc:
            log(f'it {st["it"]}: master SAT ({ts:.1f}s), NO infeasible subset of size <= {maxk} ({tsc:.0f}s) -> STALL, solution in w11_stall.json')
            json.dump(dict(b=b, names=names, labels=[f"{p}:{s_['x']}" for p, s_ in zip(pair, slots)]), open(os.path.join(HERE, 'w11b_stall.json'), 'w'))
            break
        cuts = []
        for c in newc:
            idx = st['ncuts']; st['ncuts'] += 1
            clause = encode_cut(enc, c, b, bvars, base)
            rec = dict(idx=idx, it=st['it'], E=c['E'], traces={str(F): [a for a in range(61) if b[F] >> a & 1] for F in c['E']},
                       pairs={str(F): list(pair[F]) for F in c['E']},
                       rows=[[k, [list(key[0]), list(key[1])] if k == 'L' else list(key), r, str(yv)] for (k, key, r, yv) in c['rows']],
                       kap={str(F): str(v) for F, v in c['kap'].items()}, gap=str(c['gap']), cut_clause=clause)
            json.dump(rec, open(os.path.join(CERTDIR, f'c{idx}.json'), 'w'))
            cuts.append(clause)
        allc = enc.cl + cuts; enc.cl = []; st['top'] = enc.top
        with open(cutp, 'a') as f:
            for c_ in allc: f.write(' '.join(map(str, c_)) + ' 0\n')
        for c_ in allc: s.add_clause(c_)
        sizes = sorted(len(c['E']) for c in newc)
        st['history'].append([st['it'], ts, tsc, len(newc), sizes[0], sizes[-1]])
        log(f'it {st["it"]}: master SAT ({ts:.1f}s); {len(newc)} cuts (|E| {sizes[0]}..{sizes[-1]}) scan {tsc:.0f}s; total cuts {st["ncuts"]}, aux top {st["top"]}')
        st['it'] += 1
        json.dump(st, open(stp, 'w'))
    json.dump(st, open(stp, 'w'))
    log(f'== run end it={st["it"]} cuts={st["ncuts"]} ({time.time()-T0:.0f}s)')

# ------------------------------------------------------------------------------------------------- eager L4A (prep2)
def l4a_extra(e, X, pts, P, N):
    """Lemma L4A (L on {P_k,P_l,F,G} + Lemma A for (F,G)): for new edges F,G and a base pair (k,l) with
    N_kl & F & G = {} (named; base edges contain no outside point):  |b_F&B| + |b_G&B| - |b_F&b_G&B| <= |B| - 24 = 13,
    B = P_k u P_l (|B| = 37).  Proof: L gives |F&G \\ B| <= |B| + 42 - 61 - |F&B| - |G&B|; Lemma A gives
    |F&G \\ B| >= 5 - |F&G&B|.  (|F| = |G| = 21, F&B = b_F&B.)"""
    from w8sat import Enc
    T, Fl = e.T, e.F
    ge = lambda o, k: Enc.ge(o, k, T, Fl)
    n = len(pts); cnt = 0
    for p, q in itertools.combinations(range(len(X)), 2):
        Fd, Gd = X[p], X[q]
        for (k, l), Nk in N.items():
            Bu = sorted(set(P[k]) | set(P[l])); bound = len(Bu) - 24
            pr = {a: e.AND(Fd['b'][a], Gd['b'][a]) for a in Bu}
            guard = [pr[a] for a in Nk]
            ox, oy = Fd['cnt'][k, l], Gd['cnt'][k, l]
            zc = None
            for i in range(1, len(ox) + 1):
                for j in range(1, len(oy) + 1):
                    need = i + j - bound
                    if need < 1: continue
                    if need > min(i, j):   # z <= min(x,y): z >= need impossible; clause without z
                        c = guard + [-ge(ox, i), -ge(oy, j)]
                        # minimality: skip if a smaller (i,j) already gives the same clause type -- keep simple
                    else:
                        if zc is None: zc = e.count([pr[a] for a in Bu], cap=13)   # need <= 13 here (max(i,j) <= 13)
                        c = guard + [-ge(ox, i), -ge(oy, j), ge(zc, need)]
                    e.clause(c); cnt += 1
    print('L4A clauses', cnt, flush=True)

def prep2():
    from w8sat import build
    from pysat.formula import CNF
    t = time.time(); e, X, pts, W = build('3211', tt=True, sb=True, extra=l4a_extra)
    CNF(from_clauses=e.cl).to_file(os.path.join(HERE, 'w11_base2.cnf'))
    n = len(pts); P = [[a for a in range(n) if k in pts[a][1]] for k in range(4)]
    meta = dict(names=[p[0] for p in pts], P=P, T=e.T, top=e.pool.top,
                slots=[dict(pair=list(F['pair']), x=pts[F['x']][0], b=F['b']) for F in X], nclauses=len(e.cl))
    json.dump(meta, open(os.path.join(HERE, 'w11_meta2.json'), 'w'))
    print('prep2 done', len(e.cl), e.pool.top, f'{time.time()-t:.0f}s')

if __name__ == '__main__':
    if sys.argv[1] == 'prep': prep()
    elif sys.argv[1] == 'prep2': prep2()
    else: run(float(sys.argv[2]), int(dict(a.split('=') for a in sys.argv[3:]).get('maxk', 4)))

