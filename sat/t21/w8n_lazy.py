"""Lazy (CEGAR) driver for w8n_model: L-family constraints added only when violated by the current solution.
Usage: python3 w8n_lazy.py CLS WIT [TL_PER_ITER] [MAXIT]   e.g. 2,4 A0,C0,A1,C1 60 40"""
import sys, itertools, time, json
sys.path.insert(0, 'work/e616/t21')
import w8n_model as W
from ortools.sat.python import cp_model

def val(s, x): return x if isinstance(x, int) else s.Value(x)

def run(cls, wit, tl=60, maxit=40, fam_max=4, log=print, extraJ=(), others=()):
    aa, cc = cls
    fixF = {1: (list(range(aa)) + list(range(4, 8 - aa)), list(range(cc)) + list(range(4, 8 - cc)))}
    md, Wl, nfam, nnk = W.build(cls=cls, wit=wit, fam_max=fam_max, fixF=fixF, lazy=True, extraJ=extraJ, others_wit=others)
    names = md.names; added = set(); total = 0
    for it in range(maxit):
        s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 2
        t0 = time.time(); st = s.Solve(md.m); stn = s.StatusName(st)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            log(f'it {it}: {stn} ({time.time()-t0:.1f}s) families={total}'); return stn, None
        mem = {n: [p for p in range(W.NPT) if val(s, md.E[n][p])] for n in names}
        sets = {n: set(v) for n, v in mem.items()}
        rest = {n: val(s, md.rest[n]) for n in names}
        ro = {k: val(s, v) for k, v in md.ro.items()}
        viol = []
        for k in range(3, fam_max + 1):
            for S in itertools.combinations(names, k):
                if S in added: continue
                closed = [n for n in S if rest[n] == 0 and md.rest[n] is 0]
                if not closed: continue
                if set(S) >= {'E1', 'E2'} and len(closed) == len(S): continue
                if set.intersection(*[sets[n] for n in S]): continue
                un = len(set.union(*[sets[n] for n in S]))
                varS = [n for n in S if md.rest[n] is not 0]
                b = un + sum(rest[n] for n in varS)
                if len(varS) >= 2:
                    # best (largest) tree subtraction gives the tightest bound; any tree < 61 is a violation
                    best = 0
                    for T in itertools.combinations(itertools.combinations(varS, 2), len(varS) - 1):
                        # check spanning tree
                        par = {v: v for v in varS}
                        def f(v):
                            while par[v] != v: v = par[v]
                            return v
                        ok = True
                        for x, y in T:
                            fx, fy = f(x), f(y)
                            if fx == fy: ok = False; break
                            par[fx] = fy
                        if ok: best = max(best, sum(ro[e] for e in T))
                    b -= best
                if b < 61: viol.append((b, S))
        log(f'it {it}: {stn} ({time.time()-t0:.1f}s) violated={len(viol)} families={total}')
        if not viol:
            return 'FEASIBLE', dict(mem=mem, rest=rest)
        viol.sort()
        for b, S in viol[:400]:
            total += md.add_family(S); added.add(S)
    return 'MAXIT', None

if __name__ == '__main__':
    cls = tuple(map(int, sys.argv[1].split(','))); wit = tuple(x for x in sys.argv[2].split(',') if x)
    tl = float(sys.argv[3]) if len(sys.argv) > 3 else 60; maxit = int(sys.argv[4]) if len(sys.argv) > 4 else 40
    st, sol = run(cls, wit, tl, maxit, log=lambda *a: print(*a, flush=True))
    print('RESULT', cls, wit, st, flush=True)
    if sol:
        for n, v in sol['mem'].items():
            if n in ('E1', 'E2'): continue
            print(n, 'M', [p for p in v if p < 5], 'A', [p - 5 for p in v if 5 <= p < 21], 'C', [p - 21 for p in v if 21 <= p < 37],
                  'O', [len([p for p in v if p in W.O[y]]) for y in range(5)], 'rest', sol['rest'][n])
