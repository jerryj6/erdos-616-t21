r"""Independent re-encoding (referee) of the Wave-10 N-noK4 (2,4) core, written from the mathematical statements.
Does NOT import or reuse any w9/w10x code. Only the *list of lemma instances* (which edges each instance talks about)
is read from w10x_n24s_core.json; slot identities are re-derived from labels and cross-checked.

Model: 61 named base points (constructed here from the (2,4) definition), K pool points, 19 slots = one edge avoiding
N\{y} for every base 5-pair (X,Y) with N = X&Y and every type y in N not realised by a base edge.
Slot bits x[s][a]; every slot has 21 - sum_a x[s][a] private points (in no other model edge).  All auxiliaries are
FULL equivalences (Tseitin AND, Sinz sequential counter in both directions), so the intended assignment of any real
configuration satisfies every definition clause; every non-definition clause is an exact (per-point) instance of a
lemma, conditional on its hypotheses.

usage: python3 ref_enc.py OUT.cnf [K=114] [nopool]      (POOL/SB are never used; no symmetry breaking)
"""
import sys, json, itertools, os

K = 114
for a in sys.argv[2:]:
    if a.startswith('K='): K = int(a[2:])
OUT = sys.argv[1]
CORE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 't21', 'w10x_n24s_core.json')
EDGES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 't21', 'w9_cn24.json')

# ---------------- base, class (2,4): a = |A_G & A_H| = 2, c = |C_G & C_H| = 4 ----------------
pts = []
def grp(pref, k):
    out = []
    for i in range(k):
        out.append(len(pts)); pts.append(f'{pref}{i}' if k > 1 or pref not in ('v', 'w') else pref)
    return out
v = grp('v', 1)[0]; w = grp('w', 1)[0]; m = grp('m', 3)
al = grp('al', 2); ag = grp('ag', 2); ah = grp('ah', 2); ar = grp('a0', 10)      # A = 16 points
cl = grp('cl', 4); cr = grp('c0', 12)                                              # C = 16 points, C_G = C_H = cl
og = grp('og', 12); oh = grp('oh', 12)
NN = len(pts); assert NN == 61
Mset = {v, w, *m}
E1 = frozenset(Mset | set(al + ag + ah + ar)); E2 = frozenset(Mset | set(cl + cr))
G = frozenset({v} | set(al + ag + cl + og)); H = frozenset({w} | set(al + ah + cl + oh))
BASE = [E1, E2, G, H]                      # index -1-k  <->  BASE[k]
assert all(len(b) == 21 for b in BASE)
# sanity of the defining (2,4) relations
assert G & H == set(al + cl) and len(E1 & G) == len(E2 & G) == len(E1 & H) == len(E2 & H) == 5
assert (G - E1 - E2).isdisjoint(H - E1 - E2)

bpairs = [(i, j) for i, j in itertools.combinations(range(4), 2) if len(BASE[i] & BASE[j]) == 5]
slots = []   # (i, j, y)
for (i, j) in bpairs:
    N = BASE[i] & BASE[j]
    realised = {next(iter(BASE[k] & N)) for k in range(4) if k not in (i, j) and len(BASE[k] & N) == 1}
    for y in sorted(N - realised): slots.append((i, j, y))
assert len(slots) == 19, len(slots)

# map the json slot indices 0..18 to my slots via the labels, and cross-check the avoid sets by point names
jedges = json.load(open(EDGES))['edges'][:19]
their_names = ['v', 'w', 'm0', 'm1', 'm2'] + [f'al{i}' for i in range(2)] + [f'ag{i}' for i in range(2)] + \
    [f'ah{i}' for i in range(2)] + [f'a0{i}' for i in range(10)] + [f'cl{i}' for i in range(4)] + \
    [f'c0{i}' for i in range(12)] + [f'og{i}' for i in range(12)] + [f'oh{i}' for i in range(12)]
assert their_names == pts, 'naming differs'
jmap = {}
for t, e in enumerate(jedges):
    lab = e['label']                         # 'g1:(Bi,Bj):type'
    pr, ty = lab.split(':')[1], lab.split(':')[2]
    bi, bj = [int(z.strip()[1:]) for z in pr.strip('()').split(',')]
    key = (min(bi, bj), max(bi, bj), pts.index(ty))
    s = slots.index(key)
    N = BASE[key[0]] & BASE[key[1]]
    assert set(e['avoid']) == N - {key[2]}, (lab, e['avoid'])
    jmap[t] = s
assert sorted(jmap.values()) == list(range(19))

# ---------------- CNF machinery ----------------
NP = NN + K
nv = 0; CL = []
def new():
    global nv; nv += 1; return nv
TRUE = new(); CL.append([TRUE]); FALSE = -TRUE
X = [[new() for a in range(NP)] for s in slots]
def add(c, tag=None):
    c2 = []
    for l in c:
        if l == TRUE: return
        if l == FALSE: continue
        c2.append(l)
    CL.append(c2)
cache = {}
def AND(*ls):
    ls2 = set()
    for l in ls:
        if l == FALSE: return FALSE
        if l == TRUE: continue
        if -l in ls2: return FALSE
        ls2.add(l)
    if not ls2: return TRUE
    if len(ls2) == 1: return next(iter(ls2))
    k = ('and', tuple(sorted(ls2)))
    if k in cache: return cache[k]
    z = new()
    for l in ls2: add([-z, l])
    add([z] + [-l for l in ls2])
    cache[k] = z; return z
def NOT(l): return -l
def OR(*ls): return -AND(*[-l for l in ls])
def ATLEAST(lits, k):
    """literal <-> (sum lits >= k); full Sinz sequential counter, both directions."""
    lits = [l for l in lits if l != FALSE]
    t = sum(1 for l in lits if l == TRUE); lits = sorted(l for l in lits if l != TRUE)
    k2 = k - t
    if k2 <= 0: return TRUE
    if k2 > len(lits): return FALSE
    key = ('cnt', tuple(lits))
    reg = cache.get(key)
    if reg is None or len(reg[-1]) < k2:
        # rebuild with cap = k2 (keep larger caps if requested later; small waste is fine)
        cap = max(k2, reg and len(reg[-1]) or 0)
        prev = []   # prev[j-1] <-> sum of first i lits >= j
        rows = []
        for i, l in enumerate(lits):
            cur = []
            for j in range(1, min(i + 1, cap) + 1):
                a = prev[j - 1] if j - 1 < len(prev) else FALSE       # sum_{<i} >= j
                b = (prev[j - 2] if j >= 2 else TRUE)                   # sum_{<i} >= j-1
                z = new()
                # z <-> a or (b and l)
                add([-a, z]); add([-b, -l, z]); add([-z, a, b]); add([-z, a, l])
                cur.append(z)
            prev = cur; rows.append(cur)
        reg = rows; cache[key] = reg
    return reg[-1][k2 - 1]
def ATMOST(lits, k): return -ATLEAST(lits, k + 1)
def EQ(lits, k): return AND(ATLEAST(lits, k), ATMOST(lits, k))

def bits(e):
    if e < 0:
        b = BASE[-1 - e]; return [TRUE if a in b else FALSE for a in range(NP)]
    return X[jmap[e]]
def bits_slot(s): return X[s]
def inter(*bs): return [AND(*[b[a] for b in bs]) for a in range(NP)]

counts = {}
def tag(t): counts[t] = counts.get(t, 0) + 1

# ---------------- eager part (lemmas evaluated at the base, for every slot) ----------------
for s, (i, j, y) in enumerate(slots):
    x = X[s]; N = BASE[i] & BASE[j]
    for a in N - {y}: add([-x[a]]); tag('AV')                       # tau >= 5: slot avoids N\{y}
    add([x[y]]); tag('R1')                                           # R.1: N is a transversal
    add([ATMOST(x, 21)]); tag('E21')
    for k in range(4):
        add([ATLEAST([x[a] for a in BASE[k]], 5)]); tag('A')         # Lemma A
    for k in (i, j):
        add([ATMOST([x[a] for a in BASE[k]], 5)]); tag('R3')          # R.3 at the base pair
    for (p, q) in bpairs:                                            # D1 at every base 5-pair
        Np = BASE[p] & BASE[q]
        hyp = ATMOST([x[a] for a in Np], 4)
        add([-hyp, ATMOST([x[a] for a in BASE[p] | BASE[q]], 9)]); tag('D1')
    # property L on {base subfamily S} + {slot}: no common point => union >= 61
    for r in range(1, 5):
        for S in itertools.combinations(range(4), r):
            I = frozenset.intersection(*[BASE[k] for k in S]); U = frozenset.union(*[BASE[k] for k in S])
            # union = |U| + 21 - |x & U|  >= 61  unless x meets I
            need = len(U) + 21 - 61      # |x & U| <= need
            if need >= 21: continue
            add([x[a] for a in I] + [ATMOST([x[a] for a in U], need)]); tag('Lbase')
for s, t in itertools.combinations(range(19), 2):
    xs, xt = X[s], X[t]
    st = inter(xs, xt)
    add([ATLEAST(st, 5)]); tag('A')                                  # Lemma A (privates unshared: exact)
    for k in range(4): add([st[a] for a in BASE[k]]); tag('F1')       # F1: 3-wise intersecting
    i, j, y = slots[s]; i2, j2, y2 = slots[t]
    if (i, j) == (i2, j2) and y != y2:                                # S(a)/R.3 at the base pair
        for a in range(NP):
            if a in BASE[i] or a in BASE[j]: continue
            add([-xs[a], -xt[a]]); tag('SAbase')

# ---------------- the 380 lazy lemma instances, exact per-point forms ----------------
def pair5(Xb, Yb):
    Nl = inter(Xb, Yb); return EQ(Nl, 5), Nl
def single(Zb, Nl): return EQ([AND(Zb[a], Nl[a]) for a in range(NP)], 1)
core = json.load(open(CORE))['inst']
OPT = dict(a.split('=', 1) for a in sys.argv[2:] if '=' in a)
if 'inst' in OPT: core = json.load(open(OPT['inst']))
if 'drop' in OPT: core = [i for i in core if i[0].lstrip('X') not in OPT['drop'].split(',')]
if 'fix' in OPT:      # fix slot bits to a literal configuration: {json slot index: [point indices]}
    fx = json.load(open(OPT['fix']))
    for t, S in fx.items():
        x = bits(int(t))
        for a in range(NP): add([x[a] if a in S else -x[a]])
for ins in core:
    kind = ins[0].lstrip('X')
    if kind == 'L':
        fam = ins[1]; bs = [bits(e) for e in fam]; mm = len(fam)
        com = [AND(*[b[a] for b in bs]) for a in range(NP)]
        exc = []
        for a in range(NP):
            ls = [b[a] for b in bs if b[a] != FALSE]
            for kk in range(2, len(ls) + 1): exc.append(ATLEAST(ls, kk))   # (mult-1)^+ as unary
        add(com + [ATMOST(exc, 21 * mm - 61)]); tag('L')
        continue
    Xb, Yb = bits(ins[1]), bits(ins[2])
    p5, Nl = pair5(Xb, Yb)
    if kind == 'R3':
        Zb = bits(ins[3]); hyp = AND(p5, single(Zb, Nl))
        for Wb in (Xb, Yb): add([-hyp, ATMOST(inter(Zb, Wb), 5)])
        tag('R3')
    elif kind == 'D1':
        Lb = bits(ins[3]); hyp = AND(p5, ATMOST([AND(Lb[a], Nl[a]) for a in range(NP)], 4))
        add([-hyp, ATMOST([AND(Lb[a], OR(Xb[a], Yb[a])) for a in range(NP)], 9)]); tag('D1')
    elif kind in ('SA', 'W7'):
        Z1, Z2 = bits(ins[3]), bits(ins[4])
        difftype = ATMOST([AND(Z1[a], Z2[a], Nl[a]) for a in range(NP)], 0)
        hyp = AND(p5, single(Z1, Nl), single(Z2, Nl), difftype)
        zz = inter(Z1, Z2)
        if kind == 'SA':
            for a in range(NP): add([-hyp, -zz[a], Xb[a], Yb[a]])
            tag('SA')
        else:
            add([-hyp, ATLEAST([AND(zz[a], Xb[a], -Yb[a]) for a in range(NP)], 2)])
            add([-hyp, ATLEAST([AND(zz[a], Yb[a], -Xb[a]) for a in range(NP)], 2)])
            if 'nonk' not in sys.argv: add([-hyp, ATLEAST(zz, 6)])       # NK
            tag('W7+NK')
    else:
        raise ValueError(ins)

with open(OUT, 'w') as f:
    f.write(f'p cnf {nv} {len(CL)}\n')
    for c in CL: f.write(' '.join(map(str, c)) + ' 0\n')
print(f'K={K} vars={nv} clauses={len(CL)} tags={counts}', flush=True)
json.dump({'slots': [[i, j, pts[y]] for (i, j, y) in slots], 'jmap': jmap}, open(OUT + '.map.json', 'w'))
