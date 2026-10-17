s = open('cegar2.py').read()
s = s.replace("from pysat.solvers import Solver", "from pysat.solvers import Solver\nfrom eager2 import enum as enum_cover")
s = s.replace("""        viol = find_viol(S[sel], r, 6, 30000, percap)""", """        Tsub = T[sel]
        lists = [np.nonzero((Tsub >> v) & 1)[0] for v in range(n)]
        for L in lists: rng.shuffle(L)
        sup_ptr = np.zeros(n + 1, np.int64)
        for v in range(n): sup_ptr[v + 1] = sup_ptr[v] + len(lists[v])
        sup_index = np.concatenate(lists).astype(np.int64)
        out = np.zeros((CAP, 4), np.int32)
        c = enum_cover(Tsub, n, r, sup_index, sup_ptr, out, 4)
        viol = out if c < 0 else out[:c]""")
s = s.replace("    percap = int(sys.argv[6]) if len(sys.argv) > 6 else 20",
              "    percap = int(sys.argv[6]) if len(sys.argv) > 6 else 20\n    global CAP\n    CAP = int(sys.argv[7]) if len(sys.argv) > 7 else 50000\n    assert n <= 15 and r == 21, 'm<=4 suffices only for n<=15 at r=21 (see notes)'")
s = s.replace("cegar2_", "cegar3_")
open('cegar3.py', 'w').write(s)
