r"""Wave 9: EXACT constructive model with an explicit pool of K outside points (CONSTRUCTIVE ONLY: an UNSAT here is
NOT a proof, because a real counterexample may need more than K shared outside points).
Points = 61 named base points + K pool points; every other point of an edge is private (fresh).  A model solution
is therefore a literal partial hypergraph.  Lazy loop: solve -> fill private points -> check literally
 (Lemma A; L on EVERY subfamily (DFS, exact); W7-I at every 5-pair; NK at every 5-pair if branch nok4)
 -> add the violated instances exactly -> repeat.  Edges are added by R.2 at 5-pairs of gen <= GMAX-1
(either side may be any edge; intersections may contain pool points).
usage: python3 w9pool.py BRANCH TAG K [gmax=1] [k=40] [tlim=1000]"""
import sys, os, itertools, json, time
sys.path.append("work/e616/pylib")
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w9lazy import Model, base_k4, base_nok4

class Pool(Model):
    def __init__(s, names, B, K, nk, gmax):
        super().__init__(names + [f'u{i}' for i in range(K)], B, nk=nk, gmax=gmax, flags=['clfile=/dev/null'])
        s.K = K
    def add_edge(s, avoid, gen, label):
        idx = super().add_edge(avoid, gen, label)   # E21 now counts named + pool: exact
        return idx
    def encode(s, ins):
        kind = ins[0]
        if kind == 'LAx':
            X, Y = s.bits(ins[1]), s.bits(ins[2])
            o = s.count([s.AND(X[a], Y[a]) for a in range(s.n)], 5); s.add([s.ge(o, 5)], 'LA')
        elif kind == 'Lfam':
            fam = ins[1]; bb = [s.bits(p) for p in fam]; m = len(fam)
            com = []
            for a in range(s.n):
                c = bb[0][a]
                for b in bb[1:]: c = s.AND(c, b[a])
                com.append(c)
            # L: if no common point then sum_F |F & NP| - |union & NP| <= 21 m - 61  (private points are disjoint)
            slack = 21 * m - 61
            if slack < 0: s.add(com, 'L'); return
            exc = []
            for a in range(s.n):
                lits = [b[a] for b in bb]
                o = s.count(lits, m)
                exc += o[1:]
            o = s.count(exc, slack + 1)
            s.add(com + [-s.ge(o, slack + 1)], 'L')
        elif kind == 'W7':
            # (X,Y) 5-pair, Z1,Z2 cross-type singles  ->  |Z1&Z2&(X\Y)| >= 2 and |Z1&Z2&(Y\X)| >= 2 ; NK: |Z1&Z2| >= 6
            _, p, q, z1, z2 = ins
            X, Y, A, Bv = s.bits(p), s.bits(q), s.bits(z1), s.bits(z2)
            N = [s.AND(X[a], Y[a]) for a in range(s.n)]
            o = s.count(N, 6); pre = [-s.ge(o, 5), s.ge(o, 6)]
            for b in (A, Bv):
                o = s.count([s.AND(N[a], b[a]) for a in range(s.n)], 2); pre += [-s.ge(o, 1), s.ge(o, 2)]
            ab = [s.AND(A[a], Bv[a]) for a in range(s.n)]
            pre += [s.AND(ab[a], N[a]) for a in range(s.n)]
            for (P, Q) in ((X, Y), (Y, X)):
                o = s.count([s.AND(ab[a], s.AND(P[a], -Q[a] if Q[a] not in (s.T, s.F) else (s.F if Q[a] == s.T else s.T))) for a in range(s.n)], 2)
                s.add(pre + [s.ge(o, 2)], 'W7I')
            if s.nk:
                o = s.count(ab, 6); s.add(pre + [s.ge(o, 6)], 'NK')
        else:
            super().encode(ins)

def literal(md, sol):
    nb = len(md.B)
    E = [frozenset(b) for b in md.B] + [frozenset(S) for S in sol]
    priv = [21 - len(x) for x in E]
    return E, priv

def check(md, sol, limit=300):
    E, priv = literal(md, sol); n = len(E); nb = len(md.B); out = []
    idx = lambda k: -1 - k if k < nb else k - nb
    for i, j in itertools.combinations(range(nb, n), 2):
        if len(E[i] & E[j]) < 5: out.append(['LAx', idx(i), idx(j)])
    bad = []
    def dfs(start, U, extra, I, fam):
        if len(bad) > limit: return
        if len(fam) >= 2 and not I and any(k >= nb for k in fam): bad.append(list(fam)); return
        for k in range(start, n):
            U2 = U | E[k]; ex2 = extra + priv[k]
            if len(U2) + ex2 > 60: continue
            dfs(k + 1, U2, ex2, (I & E[k]) if fam else E[k], fam + [k])
    dfs(0, frozenset(), 0, frozenset(), [])
    out += [['Lfam', [idx(k) for k in f]] for f in bad]
    for i, j in itertools.combinations(range(n), 2):
        N = E[i] & E[j]
        if len(N) != 5: continue
        sing = {}
        for k in range(n):
            if k in (i, j): continue
            t = E[k] & N
            if len(t) == 1: sing.setdefault(next(iter(t)), []).append(k)
        for t1, t2 in itertools.combinations(sing, 2):
            for a in sing[t1]:
                for b in sing[t2]:
                    AB = E[a] & E[b]
                    if len(AB & (E[i] - E[j])) < 2 or len(AB & (E[j] - E[i])) < 2 or (md.nk and len(AB) < 6):
                        if all(k < nb for k in (i, j, a, b)): continue
                        out.append(['W7', idx(i), idx(j), idx(a), idx(b)])
                        if len(out) > 3 * limit: return out
        if len(out) > 3 * limit: break
    return out

def needed(md, sol):
    E, _ = literal(md, sol); nb = len(md.B); n = len(E)
    gen = lambda k: 0 if k < nb else md.edges[k - nb]['gen']
    need = {}
    for i, j in itertools.combinations(range(n), 2):
        N = E[i] & E[j]
        if len(N) != 5: continue
        g = max(gen(i), gen(j)) + 1
        if g > md.gmax: continue
        for y in N:
            Bs = N - {y}
            if any(not (E[z] & Bs) for z in range(n)): continue
            key = tuple(sorted(Bs))
            if key not in need or need[key][0] > g: need[key] = (g, i, j, y)
    return need

if __name__ == '__main__':
    br, TAG, K = sys.argv[1], sys.argv[2], int(sys.argv[3])
    opt = dict(f.split('=', 1) for f in sys.argv[4:] if '=' in f)
    gmax = int(opt.get('gmax', 1)); kk = int(opt.get('k', 40)); tlim = float(opt.get('tlim', 1000))
    if br.startswith('k4:'): names, B = base_k4(br[3:]); nk = False
    else: a, c = map(int, br[5:].split(',')); names, B = base_nok4(a, c); nk = True
    md = Pool(names, B, K, nk, gmax)
    ck = f'w9pool_{TAG}.json'
    if os.path.exists(ck):
        st = json.load(open(ck))
        for e in st['edges']: md.add_edge(e['avoid'], e['gen'], e['label'])
        for ins in st['inst']: md.add_inst(ins)
        print('restored', len(md.edges), len(md.inst), flush=True)
    def save():
        json.dump(dict(edges=[dict(avoid=e['avoid'], gen=e['gen'], label=e['label']) for e in md.edges], inst=md.inst), open(ck + '.tmp', 'w')); os.replace(ck + '.tmp', ck)
    T0 = time.time()
    for it in range(10000):
        t0 = time.time(); r = md.solve(); ts = time.time() - t0
        if r is None:
            print(f'it {it}: UNSAT (pool K={K}; NOT a proof) edges={len(md.edges)} inst={len(md.inst)}', flush=True); save(); break
        sol, _ = r
        v = check(md, sol)
        added = sum(md.add_inst(x) for x in v[:800])
        msg = f'it {it}: SAT ({ts:.1f}s) edges={len(md.edges)} inst={len(md.inst)} cl={md.ncl} viol={len(v)} added={added}'
        if added == 0:
            E, priv = literal(md, sol)
            json.dump(dict(names=md.names, labels=[f'B{i}' for i in range(len(B))] + [e['label'] for e in md.edges],
                           edges=[sorted(md.names[a] for a in X) for X in E], private=priv), open(f'w9pool_{TAG}_real.json', 'w'))
            need = needed(md, sol)
            if not need:
                print(msg + f' -> CLOSED up to gen {gmax}: literal configuration written', flush=True); save(); break
            items = sorted(need.items(), key=lambda kv: (kv[1][0], kv[0]))[:kk]
            for key, (g, i, j, y) in items: md.add_edge(list(key), g, f'g{g}:({i},{j}):{md.names[y]}')
            msg += f' need={len(need)} +edges {len(items)}'
        print(msg, flush=True); save()
        if time.time() - T0 > tlim: print('time limit', flush=True); break
