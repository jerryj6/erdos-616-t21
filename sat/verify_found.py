"""Independent verifier for a candidate Erdos #616 construction given as core masks (npy of ints).
Builds the LITERAL r-uniform hypergraph: each core part S gets `copies` edges S + (r-|S|) fresh private vertices.
(1) tau via CP-SAT on the literal hypergraph (copies included): checks tau >= target and tau <= target.
(2) L_r: every subfamily with union <= 3r-3 has a common vertex; pure-Python DFS over literal edges (one copy per
    core part suffices: removing a duplicate copy keeps the intersection and shrinks the union).
usage: python3 verify_found.py file.npy r target [copies]"""
import sys
import numpy as np
def build(masks, r, copies):
    edges = []; nxt = 64
    for m in masks:
        core = [v for v in range(64) if m >> v & 1]
        for c in range(copies):
            priv = list(range(nxt, nxt + r - len(core))); nxt += r - len(core)
            e = frozenset(core + priv); assert len(e) == r; edges.append(e)
    return edges
def tau_check(edges, target):
    from ortools.sat.python import cp_model
    V = sorted(set().union(*edges)); res = []
    for bound in (target - 1, target):
        md = cp_model.CpModel(); x = {v: md.NewBoolVar(f"x{v}") for v in V}
        for e in edges: md.AddBoolOr([x[v] for v in e])
        md.Add(sum(x.values()) <= bound)
        s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = 600; s.parameters.num_workers = 1
        res.append(s.StatusName(s.Solve(md)))
    return res   # expect ['INFEASIBLE', 'FEASIBLE'/'OPTIMAL']
def check_L(edges, r):
    lim = 3 * r - 3; N = len(edges); viol = []
    def dfs(start, inter, uni, fam):
        for j in range(start, N):
            e = edges[j]; ni = inter & e
            if ni == inter: continue
            nu = uni | e
            if len(nu) > lim: continue
            if not ni:
                viol.append(fam + [j]); return True
            if dfs(j + 1, ni, nu, fam + [j]): return True
        return False
    for i in range(N):
        if dfs(i + 1, edges[i], edges[i], [i]): return False, viol[0]
    return True, None
if __name__ == '__main__':
    f, r, target = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    copies = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    masks = [int(x) for x in np.load(f)]
    okL, v = check_L(build(masks, r, 1), r)
    print("L_r property:", okL, "" if okL else f"violating subfamily {v}")
    print("tau<=target-1, tau<=target :", tau_check(build(masks, r, copies), target))
