r"""Wave 11 noK4: incremental REPLAY of a lazy-loop UNSAT with a DRAT proof (for instances whose fresh solve is too slow).
python3 w11n_replay.py BRANCH TAG LOG
Re-adds the checkpoint's instances (w10x_TAG.json, stored in insertion order) in the batches recorded in LOG
('built ... inst=N' then 'it k: ... inst=N'), solving after each batch exactly as the lazy loop did, on ONE CaDiCaL instance with
proof tracing.  Writes w11dc_tmp/w11dc_TAG.cnf (all clauses, same order as w11n_dratcore.py build) and w11dc_tmp/w11dc_TAG.drat
(binary DRAT).  Then  python3 w11n_dratcore.py trim TAG  /  map BRANCH TAG  as usual (map needs w11dc_TAG.map.npy from build).
drat-trim checks the proof against the FULL final clause set; if an incremental step were not valid w.r.t. it, drat-trim
fails (it cannot falsely verify)."""
import sys, os, json, time, re, shutil, tempfile
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
here = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(here, 'w11dc_tmp'); tempfile.tempdir = D
import pysolvers
from pysat.solvers import Cadical153
import w10x_exact
from w10x_exact import Exact, setup
br, TAG, LOG = sys.argv[1:4]
cnf = f'{D}/w11dc_{TAG}.cnf'; drat = f'{D}/w11dc_{TAG}.drat'
st = json.load(open(os.path.join(here, f'w10x_{TAG}.json')))
names, B, nk, edges, K, Kb = setup(br, st.get('opt', {}))
marks = []
for line in open(os.path.join(here, LOG)):
    m = re.search(r'^(built|it \d+:).*?inst=(\d+)', line)
    if m: marks.append(int(m.group(2)))
marks = sorted(set(marks)); assert marks[-1] == len(st['inst']), (marks[-1], len(st['inst']))
print('batch marks', marks, flush=True)
w10x_exact.Cadical153 = lambda: Cadical153(with_proof=True)
t0 = time.time()
md = Exact(names, B, edges, K, nk, clfile=cnf + '.body', solver=True)
done = 0
for mk in marks:
    for ins in st['inst'][done:mk]: md.add_inst(ins)
    done = mk; t1 = time.time()
    r = md.solver.solve()
    print(f'inst={done} clauses={md.ncl} {"SAT" if r else "UNSAT"} {time.time()-t1:.0f}s (total {time.time()-t0:.0f}s)', flush=True)
    if not r: break
assert not r and done == len(st['inst']), 'replay did not end UNSAT on the full instance list'
md.clf.close()
with open(cnf, 'w') as f:
    f.write(f'p cnf {md.top} {md.ncl}\n')
    with open(cnf + '.body') as g: shutil.copyfileobj(g, f)
os.remove(cnf + '.body')
pysolvers.flushpr(md.solver.prfp); md.solver.prfile.seek(0)
with open(drat, 'wb') as g: shutil.copyfileobj(md.solver.prfile, g)
print('proof bytes', os.path.getsize(drat), f'{time.time()-t0:.0f}s', flush=True)
