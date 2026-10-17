# Probe: (Q,P1)-single W of type q in Q1 with |W & C0| = 3 ?
import sys
from w7 import *
kmax, tl = int(sys.argv[1]), float(sys.argv[2])
pats = {4: [(*x12, 1), (*x13, 1), (*Q1, 2)]}
fixed = [(B(1,2,3,4), B(0), '==', 3)]
print(cegar(pats, fixed, kmax, tl, 'Wc3'))
