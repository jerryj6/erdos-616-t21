import sys, itertools, json
from k4m2 import *
tt = tuple(int(x) for x in sys.argv[1].split(','))
SPLIT = (7, 11, 13, 14, 3, 5, 9, 6, 10)
atoms = atoms_from(tt, SPLIT)
core = [(i, a) for i, a in enumerate(atoms) if a[1] in SPLIT]
WIT = {}
for i, j in itertools.combinations(range(4), 2):
    I = (1 << i) | (1 << j)
    Mij = [ai for ai, a in core if a[1] & I == I]
    for x in Mij:
        WIT[f'S{i}{j}_{atoms[x][0]}'] = [([y], 1) for y in Mij if y != x]
def run(names, tl=100):
    pats = {4 + e: WIT[nm] for e, nm in enumerate(names)}
    return solve(len(names), atoms, pats, tl=tl)
if __name__ == '__main__':
    names = sys.argv[2].split(','); tl = float(sys.argv[3]) if len(sys.argv) > 3 else 100
    st, sol, t = run(names, tl)
    print(names, st, f'{t:.1f}s', flush=True)
    if sol and '-v' in sys.argv: print(json.dumps(show(len(names), atoms, sol)))
