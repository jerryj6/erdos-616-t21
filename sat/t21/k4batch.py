import sys
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 600
sys.argv = ['x', '3,2,1,1']
from k4m2run import run
SETS = [
 'S23_ga0,S23_ga1,S23_ga2,S23_al0,S23_al1',
 'S12_v0,S12_c30,S12_ga0,S12_ga1,S12_ga2',
 'S02_v0,S02_al0,S02_al1,S02_a30,S02_a31',
 'S01_m0,S01_m1,S01_m2,S23_ga0,S23_al0',
 'S12_c30,S13_c40,S02_a30,S03_a40',
 'S12_c30,S13_c40,S23_ga0,S23_al0',
 'S02_a30,S03_a40,S23_ga0,S23_al0',
 'S01_m0,S12_c30,S13_c40,S02_a30,S03_a40',
 'S23_ga0,S23_al0,S12_c30,S02_a30,S01_m0',
]
tl = TL
for s in SETS:
    st, sol, t = run(s.split(','), tl)
    print(s, st, f'{t:.0f}s', flush=True)
