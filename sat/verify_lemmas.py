"""Check every lemma clause is an instance of L1 (|S_i cap S_j| <= K-1) or L2 (two disjoint 4-sets; n=14 only).
Usage: python verify_lemmas.py lemmas pool.npy n K"""
import sys
import numpy as np
lem, poolf = sys.argv[1], sys.argv[2]; n, K = int(sys.argv[3]), int(sys.argv[4])
T = [int(x) for x in np.load(poolf)]; X = (1 << n) - 1
c1 = c2 = bad = 0
for line in open(lem):
    l = list(map(int, line.split()))[:-1]
    if len(l) != 2 or l[0] >= 0 or l[1] >= 0: bad += 1; continue
    a, b = T[-l[0] - 1], T[-l[1] - 1]
    if bin((X ^ a) & (X ^ b)).count('1') <= K - 1: c1 += 1
    elif n == 14 and bin(a).count('1') == 4 and bin(b).count('1') == 4 and a & b == 0: c2 += 1
    else: bad += 1
print(f'L1 instances {c1}, L2 instances {c2}, bad {bad}')
