r"""Wave 11: INDEPENDENT exact re-check of every Benders cut certificate (w11b_certs/c*.json).
Does not import w11_benders.  Base sets are rebuilt from w8k4.base_named('3211') (the master's point list).
For each certificate (E, traces b*, pairs, rows with y, kappa) it checks with Fractions:
 (1) every row is a valid instance at b*: A: rhs = 5 - |b_F & b_G| > 0;  T: b_F&b_G&b_H empty, rhs 1;
     L: B' nonempty, (cap B') & (cap b_N') empty, rhs = 61 - |cup B' u cup b_N'| > 0;  stored rhs equals recomputed.
 (2) y >= 0, kappa >= 0, and for EVERY allowed column S (nonempty subset of E, no two slots of one base pair):
     sum_{rows hit by S} y <= sum_{F in S} kappa_F       (hit: A,T: S contains the key; L: S meets N')
 (3) gap = sum y*rhs - sum kappa (21 - |b*_F|) > 0.
 (4) the slots' pair labels agree with the master meta (so S(a) exclusions are between singles of one base pair).
Also (5) semantic test of the CUT CLAUSE ENCODING: for random perturbations b of the master solution, the CNF
(cut-file clauses, all edge bits fixed to b) is satisfiable iff every certificate's disjunction holds at b.
"""
import sys, os, json, glob, itertools, random
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'pylib'))
from w8k4 import base_named, PAT
pts, _ = base_named(PAT['3211']); NP = len(pts); assert NP == 61
BASE = [frozenset(a for a in range(NP) if k in pts[a][1]) for k in range(4)]
meta = json.load(open(os.path.join(HERE, 'w11_meta2.json')))  # slots/bvars identical to w11_meta.json (checked)
assert meta['names'] == [p[0] for p in pts]

def check(c):
    E = c['E']; b = {int(F): frozenset(v) for F, v in c['traces'].items()}; pair = {int(F): tuple(v) for F, v in c['pairs'].items()}
    for F in E: assert list(pair[F]) == meta['slots'][F]['pair'], 'pair label mismatch'
    for F in E: assert len(b[F]) <= 21
    rows = []
    for k, key, r, y in c['rows']:
        y = Fraction(y); assert y >= 0
        if k == 'A':
            F, G = key; assert r == 5 - len(b[F] & b[G]) and r > 0; rows.append((k, (F, G), r, y))
        elif k == 'T':
            F, G, H = key; assert not (b[F] & b[G] & b[H]) and r == 1; rows.append((k, (F, G, H), r, y))
        elif k == 'L':
            Bp, Np = key; assert len(Bp) >= 1 and len(Np) >= 1
            I = frozenset.intersection(*[BASE[i] for i in Bp]); U = frozenset().union(*[BASE[i] for i in Bp])
            for F in Np: I &= b[F]; U |= b[F]
            assert not I and r == 61 - len(U) and r > 0; rows.append((k, (tuple(Bp), tuple(Np)), r, y))
        else: raise AssertionError(k)
        for F in (key if k != 'L' else key[1]): assert F in E
    kap = {int(F): Fraction(v) for F, v in c['kap'].items()}
    assert all(v >= 0 for v in kap.values())
    ncol = 0
    for m in range(1, len(E) + 1):
        for S in itertools.combinations(E, m):
            if len({pair[F] for F in S}) < len(S): continue
            ncol += 1
            lhs = sum(y for k, key, r, y in rows if (all(x in S for x in key) if k != 'L' else any(x in S for x in key[1])))
            assert lhs <= sum(kap.get(F, 0) for F in S), ('column', S)
    gap = sum(y * r for k, key, r, y in rows) - sum(kv * (21 - len(b[F])) for F, kv in kap.items())
    assert gap > 0 and gap == Fraction(c['gap'])
    return ncol, gap


def check_generic(c, rng):
    """generic cut: (y=1 on A rows and the L row, kappa=1).  (2) column dual feasibility (trace-free);
    (6) identity check: for random traces the Farkas slack equals the compact form; (7) violated at the stored traces."""
    E = c['E']; pair = {int(F): tuple(v) for F, v in c['pairs'].items()}
    for F in E: assert list(pair[F]) == meta['slots'][F]['pair']
    g = c['generic']; kind = g['kind']; mid = g['mid']; Bp = tuple(g['Bp'])
    rows = [(k, tuple(key) if k != 'L' else (tuple(key[0]), tuple(key[1])), Fraction(y)) for k, key, r, y in c['rows']]
    kap = {int(F): Fraction(v) for F, v in c['kap'].items()}
    expectA = [tuple(sorted(E))] if kind == 'GEN2' else [tuple(sorted((x, mid))) for x in E if x != mid]
    assert sorted(key for k, key, y in rows if k == 'A') == sorted(expectA)
    assert [key for k, key, y in rows if k == 'L'] == [(Bp, tuple(sorted(E)))]
    for m in range(1, len(E) + 1):
        for S in itertools.combinations(E, m):
            if len({pair[F] for F in S}) < len(S): continue
            lhs = sum(y for k, key, y in rows if (all(x in S for x in key) if k != 'L' else any(x in S for x in key[1])))
            assert lhs <= sum(kap.get(F, 0) for F in S)
    B = frozenset().union(*[BASE[i] for i in Bp]); I0 = frozenset.intersection(*[BASE[i] for i in Bp])
    def compact(bb):   # True iff the compact inequality holds (cut satisfied, guard aside)
        U = frozenset().union(*[bb[x] for x in E])
        if kind == 'GEN2': return len(U & B) <= len(B) - 24
        F, H = [x for x in E if x != mid]
        return len(U & B) + len((bb[F] & bb[H]) - bb[mid]) <= len(B) - 8
    def farkas_ok(bb):  # sum y * linear rhs <= sum kappa * cap
        lhs = 0
        for k, key, y in rows:
            if k == 'A': lhs += y * (5 - len(bb[key[0]] & bb[key[1]]))
            else: lhs += y * (61 - len(B | frozenset().union(*[bb[x] for x in key[1]])))
        return lhs <= sum(kv * (21 - len(bb[F])) for F, kv in kap.items())
    for _ in range(200):
        bb = {x: frozenset(a for a in range(61) if rng.random() < rng.choice([0.15, 0.3, 0.5])) for x in E}
        assert compact(bb) == farkas_ok(bb)
    bs = {int(F): frozenset(v) for F, v in c['traces'].items()}
    assert not (I0 & frozenset.intersection(*[bs[x] for x in E])) and not compact(bs), 'not violated at stored traces'

def holds(c, bb):
    """the certificate's disjunction (the cut's semantic content) at traces bb (dict slot -> frozenset)."""
    if c.get('generic'):
        g = c['generic']; E = c['E']; Bp = g['Bp']
        B = frozenset().union(*[BASE[i] for i in Bp]); I0 = frozenset.intersection(*[BASE[i] for i in Bp])
        if I0 & frozenset.intersection(*[bb[x] for x in E]): return True
        U = frozenset().union(*[bb[x] for x in E])
        if g['kind'] == 'GEN2': return len(U & B) <= len(B) - 24
        F, H = [x for x in E if x != g['mid']]
        return len(U & B) + len((bb[F] & bb[H]) - bb[g['mid']]) <= len(B) - 8
    bs = {int(F): frozenset(v) for F, v in c['traces'].items()}
    for k, key, r, y in c['rows']:
        if k == 'A':
            F, G = key
            if len(bb[F] & bb[G]) >= len(bs[F] & bs[G]) + 1: return True
        elif k == 'T':
            F, G, H = key
            if bb[F] & bb[G] & bb[H]: return True
        else:
            Bp, Np = key
            I = frozenset.intersection(*[BASE[i] for i in Bp]); U = frozenset().union(*[BASE[i] for i in Bp]); Us = U
            for F in Np: I &= bb[F]; U |= bb[F]; Us |= bs[F]
            if I or len(U) >= len(Us) + 1: return True
    for F in c['kap']:
        if len(bb[int(F)]) <= len(bs[int(F)]) - 1: return True
    return False

if __name__ == '__main__':
    files = sorted(glob.glob(os.path.join(HERE, 'w11b_certs', 'c*.json')), key=lambda p: int(os.path.basename(p)[1:-5]))
    certs = [json.load(open(p)) for p in files]
    tot = 0; sizes = {}
    rng = random.Random(7); ngen = 0
    for c in certs:
        if c.get('generic'): check_generic(c, rng); ngen += 1
        else: check(c)
        tot += 1; sizes[len(c['E'])] = sizes.get(len(c['E']), 0) + 1
    print(f'certificates re-checked exactly: {tot}/{len(certs)} OK ({ngen} generic, {tot-ngen} trace-specific); |E| distribution {dict(sorted(sizes.items()))}')
    if 'enc' in sys.argv:
        from pysat.solvers import Cadical153
        cut_cl = []
        with open(os.path.join(HERE, 'w11b_cuts.cnf')) as f:
            for line in f: cut_cl.append(list(map(int, line.split()))[:-1])
        bvars = [s['b'] for s in meta['slots']]; T = meta['T']
        s = Cadical153(bootstrap_with=cut_cl + [[T]])
        # base point: a random certificate's own master solution, perturbed
        random.seed(int(dict(a.split('=') for a in sys.argv if '=' in a).get('seed', 1)))
        ntest = int(dict(a.split('=') for a in sys.argv if '=' in a).get('n', 60)); agree = 0; nsat = 0
        lastsol = json.load(open(os.path.join(HERE, 'w11b_lastsol.json')))['b']
        for t in range(ntest):
            c0 = random.choice(certs)
            bb = {F: frozenset(a for a in range(61) if lastsol[F] >> a & 1) for F in range(24)}
            for F, v in c0['traces'].items(): bb[int(F)] = frozenset(v)
            for _ in range(random.randint(0, 3)):
                F = random.randrange(24); a = random.randrange(61); bb[F] = bb[F] ^ {a}
            sem = all(holds(c, bb) for c in certs)
            ass = [bvars[F][a] if a in bb[F] else -bvars[F][a] for F in range(24) for a in range(61)]
            r = s.solve(assumptions=ass)
            assert r == sem, ('ENCODING MISMATCH', t, r, sem)
            agree += 1; nsat += sem
        print(f'cut-encoding semantic test: {agree}/{ntest} agree ({nsat} with all disjunctions true, {ntest-nsat} with some cut violated) (CNF satisfiable iff all certificate disjunctions hold)')
