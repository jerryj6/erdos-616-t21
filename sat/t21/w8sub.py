import sys, time
from w8k4 import *
pat = sys.argv[1]; sel = sys.argv[2]; tl = float(sys.argv[3]); flags = sys.argv[4:] 
pts, Osz = base(PAT[pat]); W = witnesses(pts)
nm = lambda w: f"{w[0]}{w[1]}:{pts[w[2]][0]}"
if sel == 'apex0':   # W's: singles of (0,i) with type private to P0&P_i ; Y's: singles of pairs not containing 0, type not in P0
    idx = [k for k, w in enumerate(W) if (0 in w[:2] and len(pts[w[2]][1]) == 2) or (0 not in w[:2] and 0 not in pts[w[2]][1])]
elif sel == 'all': idx = list(range(len(W)))
else: idx = [int(t) for t in sel.split(',')]
print([nm(W[k]) for k in idx], flags, flush=True)
st, t, out, _, pts2 = solve(pat, tl=tl, wsel=set(idx), named=('named' in flags), tri=('tri' in flags), workers=int(dict(f.split('=') for f in flags if '=' in f).get('w', 2)))
print(st, f'{t:.1f}s', flush=True)
if out:
    for o in out: print(nm(o[0]), o[1:], flush=True)
