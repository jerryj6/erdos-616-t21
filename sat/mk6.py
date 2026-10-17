s = open('cegar4.py').read()
old_start = s.index("    if LEMMA2:")
old_end = s.index("    lem_f.close()")
new = """    if LEMMA2:
        # Lemma L2(n) (proved in notes; r=21, m=4 window): disjoint T,T' in F with |T|+|T'| <= 3n-24-2*cmax
        # and n-|T|-|T'| <= 8 cannot coexist (P1 completes them to a violating covering quadruple/triple).
        cz = popv(T)
        bound = 3 * n - 24 - 2 * cmax
        for i in range(N):
            js = np.nonzero(((T[i+1:] & T[i]) == 0) & (cz[i+1:] + cz[i] <= bound) & (n - cz[i+1:] - cz[i] <= 8))[0] + i + 1
            for j in js:
                if popc_py(S[i] & S[j]) <= K - 1: continue  # already L1
                cl = [-(i + 1), -(int(j) + 1)]
                s.add_clause(cl); lem_f.write(f'{cl[0]} {cl[1]} 0\\n'); ncl += 1; nl2 += 1
"""
s = s[:old_start] + new + s[old_end:]
s = s.replace("LEMMA2 = (n == 14 and cmin == 4 and cmax == 5 and r == 21)", "LEMMA2 = (r == 21)")
s = s.replace("import sys, time, itertools", "import sys, time, itertools\npopc_py = lambda x: bin(int(x)).count('1')")
s = s.replace("cegar4_", "cegar6_")
open('cegar6.py', 'w').write(s)
