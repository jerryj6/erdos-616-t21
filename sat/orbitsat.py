"""Orbit-SAT search for Erdos #616 constructions (v2).
Core X=[n], permutation group G. Variables = G-orbits of core parts S with smin<=|S|<=smax.
P1 (tau>=K): every (K-1)-subset C of X is disjoint from some chosen S.
L_r: every subfamily with empty intersection has span |U S|+sum(r-|S|) >= 3r-2.
Eager-lazy: when an orbit is first chosen, all orbits incompatible with it (some images meet in <K points:
lemma L1, valid given P1+L) get binary clauses. Other violations found on the expanded family by DFS whose first
element ranges over orbit reps (valid by G-invariance), with monotone shrinking candidate lists; budgeted, then
randomized greedy probes (minimised), then a full unbudgeted DFS before any FOUND.
usage: python3 orbitsat.py n r K smin smax group [timeout]
"""
import sys, time, itertools
import numpy as np
from numba import njit
from pysat.solvers import Cadical153

@njit(cache=True)
def popc(x):
    c = 0
    while x:
        x &= x - 1
        c += 1
    return c

def closure(gens, n):
    idp = tuple(range(n))
    seen = {idp}; frontier = [idp]
    while frontier:
        nf = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[i]] for i in range(n))
                if q not in seen:
                    seen.add(q); nf.append(q)
        frontier = nf
    return np.array(sorted(seen), dtype=np.int64)

def make_group(name, n):
    if name == 'none':
        return np.array([list(range(n))], dtype=np.int64)
    if name == 'cyc':
        return closure([[(i+1) % n for i in range(n)]], n)
    if name == 'dih':
        return closure([[(i+1) % n for i in range(n)], [(-i) % n for i in range(n)]], n)
    if name.startswith('cycmult'):
        a = int(name.split(':')[1])
        return closure([[(i+1) % n for i in range(n)], [(a*i) % n for i in range(n)]], n)
    if name == 'aff':
        p = n
        g0 = next(g for g in range(2, p) if len({pow(g, k, p) for k in range(p-1)}) == p-1)
        return closure([[(i+1) % p for i in range(p)], [(g0*i) % p for i in range(p)]], n)
    if name.startswith('affsub'):
        a = int(name.split(':')[1]); p = n
        return closure([[(i+1) % p for i in range(p)], [(a*i) % p for i in range(p)]], n)
    if name == 'psl':  # PSL(2,q) on projective line, q=n-1 prime; point q = infinity
        q = n - 1; inf = q
        def f(z, a, b, c, d):
            if z == inf:
                return inf if c == 0 else (a * pow(c, -1, q)) % q
            num = (a*z + b) % q; den = (c*z + d) % q
            if den == 0: return inf
            return (num * pow(den, -1, q)) % q
        g0 = next(g for g in range(2, q) if len({pow(g, k, q) for k in range(q-1)}) == q-1)
        gens = [[f(z, 1, 1, 0, 1) for z in range(n)], [f(z, 0, q-1, 1, 0) for z in range(n)],
                [f(z, g0*g0 % q, 0, 0, 1) for z in range(n)]]
        return closure(gens, n)
    if name.startswith('semi'):  # semi:k Z_k on n/k blocks; semiw also cycles blocks; semim adds x->-x in blocks
        k = int(name.split(':')[1]); m = n // k; assert m * k == n
        gens = [[(i // k) * k + (i % k + 1) % k for i in range(n)]]
        if name.startswith('semiw'):
            gens.append([((i // k + 1) % m) * k + i % k for i in range(n)])
        if name.startswith('semim'):
            gens.append([(i // k) * k + (-(i % k)) % k for i in range(n)])
        return closure(gens, n)
    if name.startswith('pg23fix') or name.startswith('pg23sym'):  # PGL(3,3) on 13 pts + (n-13) extra pts
        import geomgroups as gg
        pts, lines, mat_pt = gg.pg_q(3)
        Ms = [[[1,1,0],[0,1,0],[0,0,1]], [[0,0,1],[1,0,0],[0,1,0]], [[2,0,0],[0,1,0],[0,0,1]]]
        gens = [mat_pt(M) + list(range(13, n)) for M in Ms]
        if name.startswith('pg23sym') and n - 13 >= 2:
            gens.append(list(range(13)) + list(range(14, n)) + [13])
            gens.append(list(range(13)) + [14, 13] + list(range(15, n)))
        return closure(gens, n)
    if name in ('pg23pl', 'pg23pld', 'pg23x2', 'ag23pl'):
        import geomgroups as gg
        if name == 'pg23pl': gens = gg.gens_pg_pl(3)[0]
        elif name == 'pg23pld': gens = gg.gens_pg_pl(3, True)[0]
        elif name == 'pg23x2': gens = gg.gens_pg_x2(3)
        else: gens = gg.gens_ag23_pl()
        assert len(gens[0]) == n
        return closure(gens, n)
    if name in ('pgl34', 'pgaml34'):
        import pg24
        gens = pg24.gens if name == 'pgaml34' else pg24.gens[:4]
        return closure(gens, n)
    if name.startswith('sym:'):
        parts = [int(x) for x in name[4:].split(',')]
        gens = []; off = 0
        for p in parts:
            if p >= 2:
                g = list(range(n)); g[off:off+p] = list(range(off+1, off+p)) + [off]; gens.append(g)
                g = list(range(n)); g[off], g[off+1] = off+1, off; gens.append(g)
            off += p
        return closure(gens, n)
    raise ValueError(name)

@njit(cache=True)
def apply(perm, m, n):
    r = 0
    for i in range(n):
        if m >> i & 1:
            r |= 1 << perm[i]
    return r

@njit(cache=True)
def orbit_reps(G, n, smin, smax):
    out = []
    for m in range(1 << n):
        pc = popc(m)
        if pc < smin or pc > smax:
            continue
        ok = True
        for gi in range(1, G.shape[0]):
            if apply(G[gi], m, n) < m:
                ok = False; break
        if ok:
            out.append(m)
    return np.array(out, dtype=np.int64)

@njit(cache=True)
def canon(G, m, n):
    best = m
    for gi in range(G.shape[0]):
        x = apply(G[gi], m, n)
        if x < best: best = x
    return best

@njit(cache=True)
def self_ok(G, reps, n, K):
    ok = np.ones(reps.shape[0], np.bool_)
    for i in range(reps.shape[0]):
        s = reps[i]
        for gi in range(G.shape[0]):
            if popc(s & apply(G[gi], s, n)) < K:
                ok[i] = False; break
    return ok

@njit(cache=True)
def p1_cover(reps, C4, C4orb, nC):
    M = np.zeros((reps.shape[0], nC), np.bool_)
    for i in range(reps.shape[0]):
        s = reps[i]
        for j in range(C4.shape[0]):
            if (s & C4[j]) == 0:
                M[i, C4orb[j]] = True
    return M

@njit(cache=True)
def all_images(G, reps, n):
    out = np.empty((reps.shape[0], G.shape[0]), np.int64)
    for i in range(reps.shape[0]):
        for g in range(G.shape[0]):
            out[i, g] = apply(G[g], reps[i], n)
    return out

@njit(cache=True)
def incompat(o, reps, imgs, ok, K):
    s = reps[o]
    res = []
    for p in range(reps.shape[0]):
        if not ok[p] or p == o:
            continue
        for g in range(imgs.shape[1]):
            if popc(s & imgs[p, g]) < K:
                res.append(p); break
    return res

@njit(cache=True)
def find_viol_lists(S, starts, r, maxdepth, cap, budget=-1):
    """All (up to cap) violating subfamilies whose first member is in starts. DFS with shrinking candidate lists:
    'span <= 3r-3' and 'must strictly shrink the intersection' are both monotone along a branch.
    Returns (rows, cnt); cnt = -1-found if the budget ran out."""
    N = S.shape[0]
    lim = 3 * r - 3
    out = np.full((cap, maxdepth), -1, np.int64)
    cnt = 0
    w = np.empty(N, np.int64)
    for i in range(N):
        w[i] = r - popc(S[i])
    L = np.empty((maxdepth + 1, N), np.int64)
    Ln = np.zeros(maxdepth + 1, np.int64)
    pos = np.zeros(maxdepth + 1, np.int64)
    inter = np.empty(maxdepth + 1, np.int64)
    uni = np.empty(maxdepth + 1, np.int64)
    ws = np.empty(maxdepth + 1, np.int64)
    chosen = np.empty(maxdepth + 1, np.int64)
    for s0 in starts:
        if cnt >= cap:
            break
        inter[0] = S[s0]; uni[0] = S[s0]; ws[0] = w[s0]; chosen[0] = s0
        c = 0
        for l in range(N):
            if (S[l] & inter[0]) != inter[0] and popc(uni[0] | S[l]) + ws[0] + w[l] <= lim:
                L[1, c] = l; c += 1
        Ln[1] = c; pos[1] = 0
        d = 1
        while d >= 1:
            if pos[d] >= Ln[d] or d > maxdepth - 1:
                d -= 1
                continue
            j = L[d, pos[d]]; pos[d] += 1
            I = inter[d-1] & S[j]
            U = uni[d-1] | S[j]
            W = ws[d-1] + w[j]
            chosen[d] = j
            if I == 0:
                if cnt < cap:
                    for t in range(d+1):
                        out[cnt, t] = chosen[t]
                cnt += 1
                if cnt >= cap:
                    break
                continue
            if budget >= 0:
                budget -= Ln[d] - pos[d]
                if budget < 0:
                    return out[:min(cnt, cap)], -1 - cnt
            c = 0
            for q in range(pos[d], Ln[d]):
                l = L[d, q]
                if (S[l] & I) != I and popc(U | S[l]) + W + w[l] <= lim:
                    L[d+1, c] = l; c += 1
            if c > 0 and d + 1 <= maxdepth - 1:
                inter[d] = I; uni[d] = U; ws[d] = W
                Ln[d+1] = c; pos[d+1] = 0
                d += 1
    return out[:min(cnt, cap)], cnt

@njit(cache=True)
def greedy_viol(S, starts, r, maxdepth, tries, seed):
    np.random.seed(seed)
    N = S.shape[0]; lim = 3 * r - 3
    out = np.full((tries, maxdepth), -1, np.int64); cnt = 0
    w = np.empty(N, np.int64)
    for i in range(N):
        w[i] = r - popc(S[i])
    for t in range(tries):
        s0 = starts[np.random.randint(starts.shape[0])]
        I = S[s0]; U = S[s0]; W = w[s0]
        fam = np.full(maxdepth, -1, np.int64); fam[0] = s0
        for d in range(1, maxdepth):
            best = 1 << 30; bj = -1; nb = 0
            for j in range(N):
                pi = popc(I & S[j])
                if pi == popc(I):
                    continue
                sp = popc(U | S[j]) + W + w[j]
                if sp > lim:
                    continue
                score = pi * 64 + sp
                if score < best:
                    best = score; bj = j; nb = 1
                elif score == best:
                    nb += 1
                    if np.random.randint(nb) == 0:
                        bj = j
            if bj < 0:
                break
            I &= S[bj]; U |= S[bj]; W += w[bj]; fam[d] = bj
            if I == 0:
                out[cnt] = fam; cnt += 1
                break
    return out[:cnt], cnt

def minimize(S, row, r):
    fam = [int(x) for x in row if x >= 0]
    def viol(f):
        I = -1; U = 0; W = 0
        for j in f:
            I &= int(S[j]); U |= int(S[j]); W += r - bin(int(S[j])).count('1')
        return I == 0 and bin(U).count('1') + W <= 3 * r - 3
    changed = True
    while changed:
        changed = False
        for j in list(fam):
            g = [x for x in fam if x != j]
            if len(g) >= 2 and viol(g):
                fam = g; changed = True; break
    return fam + [-1] * (len(row) - len(fam))

def expand(G, reps, chosen, n):
    S = []; oid = []
    for o in chosen:
        imgs = sorted({int(apply(G[gi], int(reps[o]), n)) for gi in range(G.shape[0])})
        S += imgs; oid += [o] * len(imgs)
    return np.array(S, dtype=np.int64), np.array(oid, dtype=np.int64)

def run(n, r, K, smin, smax, gname, timeout=3600, log=print, maxdepth=14):
    t0 = time.time()
    G = make_group(gname, n)
    reps = orbit_reps(G, n, smin, smax)
    ok = self_ok(G, reps, n, K)
    log(f"n={n} r={r} K={K} S in [{smin},{smax}] group={gname} |G|={len(G)} orbits={len(reps)} selfok={ok.sum()} ({time.time()-t0:.1f}s)")
    C4 = np.array([sum(1 << v for v in c) for c in itertools.combinations(range(n), K-1)], dtype=np.int64)
    cmap = {}; corb = np.empty(len(C4), np.int64)
    for j, c in enumerate(C4):
        cc = int(canon(G, int(c), n))
        corb[j] = cmap.setdefault(cc, len(cmap))
    M = p1_cover(reps, C4, corb, len(cmap))
    solver = Cadical153()
    nv = len(reps)
    for i in range(nv):
        if not ok[i]:
            solver.add_clause([-(i+1)])
    for c in range(len(cmap)):
        cl = [int(i+1) for i in np.nonzero(M[:, c] & ok)[0]]
        if not cl:
            log("P1 impossible: some (K-1)-set orbit uncovered -> UNSAT"); return 'UNSAT', None
        solver.add_clause(cl)
    try:
        solver.set_phases([-(i+1) for i in range(nv)])
    except Exception:
        pass
    it = 0; ncl = 0
    imgs = all_images(G, reps, n); expanded = set(); npair = 0
    while True:
        if time.time() - t0 > timeout:
            log(f"TIMEOUT it={it} clauses={ncl}"); return 'TIMEOUT', None
        if not solver.solve():
            log(f"UNSAT it={it} lazy clauses={ncl} ({time.time()-t0:.1f}s)"); return 'UNSAT', None
        model = solver.get_model()
        pos = {l for l in model if l > 0}
        chosen = [i for i in range(nv) if (i+1) in pos]
        newo = [o for o in chosen if o not in expanded]
        if newo:
            cs = set(chosen); conflict = False
            for o in newo:
                expanded.add(o)
                for p in incompat(o, reps, imgs, ok, K):
                    solver.add_clause([-(o+1), -(p+1)]); npair += 1
                    if p in cs: conflict = True
            if conflict:
                it += 1
                continue
        S, oid = expand(G, reps, chosen, n)
        starts = np.array([int(np.searchsorted(oid, o)) for o in chosen], dtype=np.int64)
        out, cnt = find_viol_lists(S, starts, r, maxdepth, 2000, 300_000_000)
        kind = 'dfs'
        if cnt < 0:
            cnt = -1 - cnt
            if cnt == 0:
                out, cnt = greedy_viol(S, starts, r, maxdepth, 200, it)
                if cnt:
                    out = np.array([minimize(S, row, r) for row in out], dtype=np.int64).reshape(-1, maxdepth)
                kind = 'greedy'
            if cnt == 0:
                out, cnt = find_viol_lists(S, starts, r, maxdepth, 2000, -1)
                kind = 'fulldfs'
        if cnt == 0:
            log(f"FOUND it={it} chosen orbits={len(chosen)} sets={len(S)} ({time.time()-t0:.1f}s)")
            return 'FOUND', S
        out = np.where(out >= 0, oid[np.maximum(out, 0)], -1)
        new = set()
        for row in out:
            new.add(tuple(sorted({int(x) for x in row if x >= 0})))
        for cl in new:
            solver.add_clause([-(x+1) for x in cl])
        ncl += len(new); it += 1
        if it % 20 == 0:
            log(f"  it={it} chosen={len(chosen)} sets={len(S)} kind={kind} new={len(new)} total={ncl} pairs={npair} expanded={len(expanded)} ({time.time()-t0:.1f}s)")

if __name__ == '__main__':
    a = sys.argv
    n, r, K, smin, smax = map(int, a[1:6]); g = a[6]
    to = float(a[7]) if len(a) > 7 else 3600
    st, S = run(n, r, K, smin, smax, g, to)
    if st == 'FOUND':
        fn = f"FOUND_orbit_n{n}_r{r}_K{K}_{g.replace(':','-').replace(',','_')}.npy"
        np.save(fn, S); print("saved", fn)
