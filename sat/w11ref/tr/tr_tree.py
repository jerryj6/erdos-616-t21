"""(hedge, preferred) per root case r: DFS refutation of Φ_33 ∧ x_r by propagation + branching on COV, emitted as DRAT.
Propagation at a node with cube c (signed literals): positive unit from a COV with one live literal; ¬s for every conflict
neighbour s of a true trace; RUP elimination ¬t when every live avoider of some needed B conflicts with t. A node whose
propagation empties some COV(B) is a leaf. Otherwise branch on the unsatisfied needed B with fewest live avoiders
t_1..t_m: child i has cube c ∪ {t_i, ¬t_1..¬t_{i-1}}.
DRAT: at a node, each derived literal u as the lemma (u ∨ ¬c); the node is closed by the lemma (¬c), which is RUP from the
children's closing lemmas and COV(B) (leaf: from the node's own lemmas and the emptied COV). Root cube = {x_r} with x_r a unit
of the case CNF; final lemma = empty clause. Case CNF = all COV + unit x_r + every CONF clause (t,s) of Φ that a justification
can use (subset of Φ). usage: python3 tr_tree.py TAG K"""
import sys, json, itertools, time, numpy as np, numba as nb
tag, K = sys.argv[1], int(sys.argv[2])
U = np.load(f'st_{tag}.npz'); tr = U['tr']; P = U['P']; NT = len(tr); n = int(P[0] | P[1] | P[2] | P[3]).bit_length()
pairs = np.load(f'pairs_{tag}.npy')
W = (NT + 63) // 64
Cb = np.zeros((NT, W), np.uint64)
def setbits(a, b):
    np.bitwise_or.at(Cb, (a, b // 64), (np.uint64(1) << (b % 64).astype(np.uint64)))
setbits(pairs[:, 0], pairs[:, 1]); setbits(pairs[:, 1], pairs[:, 0])
need = np.array([B for B in (sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), 4)) if all(B & int(P[q]) for q in range(4))], np.int64)
avl = [np.nonzero((tr & B) == 0)[0] for B in need]
ast = np.zeros(len(need) + 1, np.int64); ast[1:] = np.cumsum([len(a) for a in avl]); alst = np.concatenate(avl).astype(np.int64)

@nb.njit(cache=True)
def isconf(Cb, a, b):
    return (Cb[a, b >> 6] >> np.uint64(b & 63)) & np.uint64(1)

@nb.njit(cache=True)
def prop(val, Cb, ast, alst, tr, need, NT, W, out, just):
    """val: int8 (1 true / -1 false / 0 open), modified in place. out: derived signed lits (1-based); just: (t, k) pairs,
    k >= 0: elimination by need k; k = -1: neighbour of true t (just holds (t, s)). Returns (nout, njust, wipe_k or -1)."""
    no = 0; nj = 0
    # neighbours of currently true traces (cube trues) must be false
    for t in range(NT):
        if val[t] == 1:
            for s in range(NT):
                if val[s] == 0 and isconf(Cb, t, s):
                    val[s] = -1; out[no] = -(s + 1); no += 1; just[nj, 0] = t; just[nj, 1] = -1 - s; nj += 1
    X = np.empty(W, np.uint64)
    ch = True
    while ch:
        ch = False
        for k in range(len(need)):
            sat = False; cnt = 0; last = -1
            for i in range(ast[k], ast[k + 1]):
                s = alst[i]
                if val[s] == 1: sat = True; break
                if val[s] == 0: cnt += 1; last = s
            if sat: continue
            if cnt == 0: return no, nj, k
            if cnt == 1:
                t = last; val[t] = 1; out[no] = t + 1; no += 1; ch = True
                for s in range(NT):
                    if val[s] == 0 and isconf(Cb, t, s):
                        val[s] = -1; out[no] = -(s + 1); no += 1; just[nj, 0] = t; just[nj, 1] = -1 - s; nj += 1
                continue
            for w in range(W): X[w] = ~np.uint64(0)
            for i in range(ast[k], ast[k + 1]):
                s = alst[i]
                if val[s] == 0:
                    for w in range(W): X[w] &= Cb[s, w]
            for w in range(W):
                x = X[w]
                while x:
                    bit = 0
                    y = x
                    while (y & np.uint64(1)) == 0:
                        y >>= np.uint64(1); bit += 1
                    x &= x - np.uint64(1)
                    t = w * 64 + bit
                    if t >= NT or val[t] != 0 or (tr[t] & need[k]) == 0: continue
                    val[t] = -1; out[no] = -(t + 1); no += 1; just[nj, 0] = t; just[nj, 1] = k; nj += 1; ch = True
    return no, nj, -1

pl = json.load(open(f'case_{tag}_plan.json')); r = pl['reps'][K][0]
name = f'tree_{tag}_{K}'
out = np.zeros(NT + 5, np.int64); just = np.zeros((NT + 5, 2), np.int64)
lemmas = []; J = []; nodes = 0; leaves = 0; maxd = 0; t0 = time.time()
def node(val, cube, depth):
    global nodes, leaves, maxd
    nodes += 1; maxd = max(maxd, depth)
    no, nj, wk = prop(val, Cb, ast, alst, tr, need, NT, W, out, just)
    neg = [-l for l in cube]
    for u in out[:no].tolist(): lemmas.append([u] + neg)
    J.append(just[:nj].copy())
    if wk < 0:
        best = None
        for k in range(len(need)):
            a = avl[k]
            if (val[a] == 1).any(): continue
            live = a[val[a] == 0]
            if best is None or len(live) < len(best): best = live
        prev = []
        for t in best.tolist():
            v2 = val.copy(); v2[t] = 1
            for p in prev: v2[p] = -1
            node(v2, cube + [t + 1] + [-(p + 1) for p in prev], depth + 1)
            prev.append(t)
    else:
        leaves += 1
    lemmas.append(neg)
    if nodes % 50 == 0: print(name, 'nodes', nodes, 'leaves', leaves, 'depth', maxd, '%.0fs' % (time.time() - t0), flush=True)
val = np.zeros(NT, np.int8); val[r] = 1
sys.setrecursionlimit(10000)
node(val, [r + 1], 0)
# justification clauses: (t,k>=0): CONF (t,s) for avoiders s of need k conflicting with t; (t,-1-s): CONF (t,s)
Jall = np.concatenate(J) if J else np.zeros((0, 2), np.int64)
keys = set()
C = None
for t, k in Jall.tolist():
    if k >= 0:
        a = avl[k]; m = ((Cb[t, a // 64] >> (a % 64).astype(np.uint64)) & np.uint64(1)).astype(bool)
        for s in a[m].tolist(): keys.add((min(t, s), max(t, s)))
    else:
        s = -1 - k; keys.add((min(t, s), max(t, s)))
with open(name + '.cnf', 'w') as fh:
    fh.write(f'p cnf {NT} {len(need) + 1 + len(keys)}\n')
    for a in avl: fh.write(' '.join(str(x + 1) for x in a) + ' 0\n')
    fh.write(f'{r + 1} 0\n')
    for s, t in keys: fh.write(f'-{s + 1} -{t + 1} 0\n')
with open(name + '.drat', 'w') as fh:
    for L in lemmas: fh.write(' '.join(map(str, L)) + ' 0\n')
    fh.write('0\n')
print(name, 'r', r, 'DONE nodes', nodes, 'leaves', leaves, 'max depth', maxd, 'lemmas', len(lemmas), 'CONF in CNF', len(keys), '%.0fs' % (time.time() - t0), flush=True)
