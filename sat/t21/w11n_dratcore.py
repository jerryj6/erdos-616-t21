r"""Wave 11 noK4: instance core via DRAT (for checkpoints too large for assumption-based core extraction, w10x_core.py).
Phases (each a separate process, each < 20 min, memory-lean):
  python3 w11n_dratcore.py build BRANCH TAG   -> /tmp/w11dc_TAG.cnf  + w11dc_TAG.map.npy (instance id per clause, -1 = eager/def)
  python3 w11n_dratcore.py solve TAG          -> /tmp/w11dc_TAG.drat (binary DRAT from CaDiCaL 1.5.3, streamed, no list in RAM)
  python3 w11n_dratcore.py trim TAG           -> drat-trim -c /tmp/w11dc_TAG.core (clauses used by the verified proof)
  python3 w11n_dratcore.py map BRANCH TAG     -> w10x_TAG_dcore.json (checkpoint format; inst = every instance owning a core clause)
The output is only a CANDIDATE instance list: it is then certified from scratch by w10x_cert.py (independent rebuild + DRAT +
drat-trim), so nothing here needs to be trusted.  Clauses identical across instances map to ALL owners (conservative)."""
import sys, os, json, time, subprocess, shutil
import numpy as np
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
here = os.path.dirname(os.path.abspath(__file__))
ph = sys.argv[1]
if ph in ('build', 'map'): br, TAG = sys.argv[2], sys.argv[3]
else: TAG = sys.argv[2]
D = os.path.join(here, 'w11dc_tmp'); cnf = f'{D}/w11dc_{TAG}.cnf'; drat = f'{D}/w11dc_{TAG}.drat'; core = f'{D}/w11dc_{TAG}.core'
mapf = os.path.join(here, f'w11dc_{TAG}.map.npy')
t0 = time.time()
if ph == 'build':
    from w10x_exact import Exact, setup
    st = json.load(open(os.path.join(here, f'w10x_{TAG}.json')))
    names, B, nk, edges, K, Kb = setup(br, st.get('opt', {}))
    owner = []
    class E(Exact):
        cur = -1
        def add(s, c, tag):
            if s.T in c: return
            n0 = s.ncl; Exact.add(s, c, tag)
            if s.ncl > n0: owner.append(-1 if tag.split(':')[0] == 'def' else s.cur)
    body = cnf + '.body'
    md = E(names, B, edges, K, nk, clfile=body, solver=False)
    for i, ins in enumerate(st['inst']): md.cur = i; md.add_inst(ins)
    md.clf.close()
    assert len(owner) == md.ncl, (len(owner), md.ncl)
    with open(cnf, 'w') as f:
        f.write(f'p cnf {md.top} {md.ncl}\n')
        with open(body) as g: shutil.copyfileobj(g, f)
    os.remove(body)
    np.save(mapf, np.array(owner, dtype=np.int32))
    print(f'build K={K} (KB {Kb}) inst={len(st["inst"])} vars={md.top} clauses={md.ncl} non-def owned={sum(1 for o in owner if o >= 0)} {time.time()-t0:.0f}s', flush=True)
elif ph == 'solve':
    import tempfile; tempfile.tempdir = D   # proof temp file on /workspace, not in RAM-backed /tmp
    from pysat.solvers import Cadical153
    import pysolvers
    s = Cadical153(with_proof=True)
    with open(cnf) as f:
        next(f)
        for line in f: s.add_clause([int(t) for t in line.split()[:-1]])
    print(f'loaded {time.time()-t0:.0f}s', flush=True)
    r = s.solve(); print('solve', 'SAT' if r else 'UNSAT', f'{time.time()-t0:.0f}s', flush=True)
    if not r:
        pysolvers.flushpr(s.prfp); s.prfile.seek(0)
        with open(drat, 'wb') as g: shutil.copyfileobj(s.prfile, g)
        print('proof bytes', os.path.getsize(drat), flush=True)
    s.delete()
elif ph == 'trim':
    dt = subprocess.run(['timeout', '1100', os.path.join(here, '..', 'tools', 'drat-trim'), cnf, drat, '-c', core],
                        capture_output=True, text=True)
    print('\n'.join(l for l in dt.stdout.splitlines() if l.startswith('s ') or 'core' in l.lower() or 'erif' in l), flush=True)
    print(f'drat-trim {time.time()-t0:.0f}s', flush=True)
elif ph == 'map':
    owner = np.load(mapf)
    idx = {}
    with open(cnf) as f:
        next(f)
        for k, line in enumerate(f):
            o = int(owner[k])
            if o < 0: continue
            key = hash(tuple(sorted(int(t) for t in line.split()[:-1])))
            idx.setdefault(key, set()).add(o)
    used = set(); nc = 0; hit = 0
    with open(core) as f:
        for line in f:
            if line.startswith(('p', 'c')): continue
            nc += 1
            key = hash(tuple(sorted(int(t) for t in line.split()[:-1])))
            if key in idx: hit += 1; used |= idx[key]
    st = json.load(open(os.path.join(here, f'w10x_{TAG}.json')))
    out = dict(st); out['inst'] = [st['inst'][i] for i in sorted(used)]; out['core_of'] = f'w10x_{TAG}.json'; out['core_method'] = 'drat-trim -c'
    json.dump(out, open(os.path.join(here, f'w10x_{TAG}_dcore.json'), 'w'))
    from collections import Counter
    print(f'core clauses {nc}, owned hits {hit}, instances {len(used)}', dict(Counter(st['inst'][i][0] for i in used)), f'{time.time()-t0:.0f}s', flush=True)
