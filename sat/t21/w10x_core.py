"""Core extraction for an UNSAT w10x checkpoint: python3 w10x_core.py BRANCH TAG [rounds=3] [drop=KIND,..]
Rebuilds the model; every NON-definitional clause of lazy instance i gets a selector literal -s_i (the eager base
part stays hard).  Solves under the assumptions {s_i}, takes the UNSAT core, and re-solves on the core (rounds times).
Writes w10x_TAG_core.json (same format as the checkpoint, inst = core instances) for w10x_cert.py core=...
With drop=KIND the instances of that kind are left out entirely (control: is the kind needed?)."""
import sys, os, json, time
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from w10x_exact import Exact, setup
br, TAG = sys.argv[1], sys.argv[2]
opt = dict(f.split('=', 1) for f in sys.argv[3:] if '=' in f)
here = os.path.dirname(os.path.abspath(__file__))
src = opt.get('src_ck', f'w10x_{TAG}.json')
st = json.load(open(os.path.join(here, src)))
names, B, nk, edges, K, Kb = setup(br, st.get('opt', {}))
drop = set(opt.get('drop', '').split(',')) - {''}
inst = [i for i in st['inst'] if i[0].lstrip('X') not in drop]
class SelExact(Exact):
    cur = None
    def add(s, c, tag):
        if s.cur is not None and tag.split(':')[0] != 'def' and s.T not in c: c = list(c) + [-s.cur]
        Exact.add(s, c, tag)
t0 = time.time()
md = SelExact(names, B, edges, K, nk)
# R1 points must not lie in a symmetry class (SB soundness check)
symp = set(a for cl in md.symclasses for a in cl)
r1 = set(y for e in md.edges for (i, j, y) in e['groups'])
print('SB check: R1 points inside a symmetry class:', sorted(r1 & symp), flush=True)
sel = []
for ins in inst:
    v = md.newv(); md.cur = v; md.add_inst(ins); sel.append(v)
md.cur = None
print(f'built {time.time()-t0:.0f}s K={K} (bound {Kb}) instances {len(inst)} (dropped kinds {sorted(drop)}) clauses {md.ncl}', flush=True)
act = list(range(len(inst)))
for rd in range(int(opt.get('rounds', 3))):
    t1 = time.time()
    r = md.solver.solve(assumptions=[sel[i] for i in act])
    print(f'round {rd}: {"SAT" if r else "UNSAT"} ({time.time()-t1:.0f}s) on {len(act)} instances', flush=True)
    if r: break
    core = set(md.solver.get_core())
    act = [i for i in act if sel[i] in core]
    out = dict(st); out['inst'] = [inst[i] for i in act]; out['core_of'] = src; out['dropped'] = sorted(drop)
    json.dump(out, open(os.path.join(here, f'w10x_{TAG}_core.json'), 'w'))
    from collections import Counter
    print('  core size', len(act), dict(Counter(inst[i][0] for i in act)), flush=True)
