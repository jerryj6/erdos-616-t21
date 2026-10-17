# Guided probe: W (type q in Q1 at (Q,P1)) with |W&C0|=3, plus guided witnesses
import sys
from w7 import *
kmax, tl, guide = int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
W = 4; WC0 = (B(1,2,3,W), B(0)); Wq = (B(0,1,W), B(2,3))
G = {'Wo': [(*Wq, 1), (*WC0, 3)], 'Y12': [(*x12, 1), (*WC0, 3)], 'Y13': [(*x13, 1), (*WC0, 3)],
     'Y23': [(*x23, 1), (*WC0, 3)], 'J': [(*C0, 4)]}
pats = {4: [(*x12, 1), (*x13, 1), (*Q1, 2)]}; k = 5
for g in guide.split(','):
    pats[k] = G[g]; k += 1
fixed = [(B(1,2,3,4), B(0), '==', 3)]
print(cegar(pats, fixed, kmax, tl, 'Wc3g ' + guide))
