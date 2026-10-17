import numpy as np
S = set()
for K in range(8):
    for line in open(f'tree_33_{K}.cnf'):
        L = line.split()
        if len(L) == 3 and L[0][0] == '-' and L[1][0] == '-':
            a, b = sorted((-int(L[0]) - 1, -int(L[1]) - 1)); S.add((a, b))
np.save('pairs_33tree.npy', np.array(sorted(S), np.int64)); print('distinct CONF clauses used by the 8 tree CNFs', len(S))
