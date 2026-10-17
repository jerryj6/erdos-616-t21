"""Wave 12 (resume): named 4-sets that are transversals of EVERY given realization (selection heuristic only)."""
import sys, json, itertools
fs = sys.argv[1:]
Rs = [json.load(open(f)) for f in fs]
core = sorted(set(n for R in Rs for n in R['names'] if n[0] in 'Tp'))
common = None
for R in Rs:
    E = [set(e) for e in R['edges']]
    T = set(B for B in itertools.combinations(core, 4) if all(e & set(B) for e in E))
    common = T if common is None else common & T
    print(R.get('tag', ''), len(T), len(common))
json.dump(sorted(common), open('/tmp/common.json', 'w'))
for B in sorted(common): print(B)
