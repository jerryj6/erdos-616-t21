s = open('cegar3.py').read()
# add lemma clauses after covering-pair clauses
s = s.replace("""    P(f'{tag}: pool {N}, base clauses {ncl}')""", """    # Lemma L1 (proved in notes): two edges whose cores meet in <= K-1 points cannot coexist with P1.
    pc = np.array([bin(x).count('1') for x in range(1 << 16)], dtype=np.int64)
    popv = lambda a: pc[a & 0xFFFF] + pc[(a >> 16) & 0xFFFF]
    nl1 = 0
    for i in range(N):
        bad = np.nonzero(popv(S[i] & S[i+1:]) <= K - 1)[0] + i + 1
        for j in bad:
            if (T[i] | T[j]) == X: continue  # already added as covering pair
            cl = [-(i + 1), -(int(j) + 1)]
            s.add_clause(cl); lem_f.write(f'{cl[0]} {cl[1]} 0\\n'); ncl += 1; nl1 += 1
    nl2 = 0
    if LEMMA2:
        # Lemma L2 (n=14, c in {4,5}, r=21; proved in notes): no two disjoint 4-sets both chosen.
        f4 = np.nonzero(popv(T) == 4)[0]
        for a in range(len(f4)):
            i = f4[a]
            js = f4[a+1:][(T[f4[a+1:]] & T[i]) == 0]
            for j in js:
                cl = [-(int(i) + 1), -(int(j) + 1)]
                s.add_clause(cl); lem_f.write(f'{cl[0]} {cl[1]} 0\\n'); ncl += 1; nl2 += 1
    lem_f.close()
    P(f'{tag}: pool {N}, base clauses {ncl} (L1 {nl1}, L2 {nl2})')""")
s = s.replace("""    cl_f = open(f'cegar3_{tag}.clauses', 'w')""", """    cl_f = open(f'cegar4_{tag}.clauses', 'w')
    lem_f = open(f'cegar4_{tag}.lemmas', 'w')""")
s = s.replace("    global CAP", "    global CAP, LEMMA2\n    LEMMA2 = (n == 14 and cmin == 4 and cmax == 5 and r == 21)")
s = s.replace("cegar3_", "cegar4_")
s = s.replace("""        with open(f'cegar4_{tag}.clauses') as g:
            for line in g: f.write(line)""", """        for fn in (f'cegar4_{tag}.clauses', f'cegar4_{tag}.lemmas'):
            with open(fn) as g:
                for line in g: f.write(line)""")
open('cegar4.py', 'w').write(s)
