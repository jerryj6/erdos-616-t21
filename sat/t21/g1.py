from venn2 import *
# E1=0,E2=1; F's for points of M
pats = {2: [(B(0,1),0,4)],
        3: [(B(0,1,2),0,1),(B(0,1),B(2),3)],
        4: [(B(0,1,2),0,1),(B(0,1,3),0,1),(B(0,1),B(2,3),2)]}
for k in (5,):
    st, sol, t = run(k, pats, 60); print(k, st, round(t,1)); print(show(k, sol) if sol else '')
# witness for 5-pair (E1,F2): avoid x2 and 3 points of A_2
pats[5] = [(B(0,1,2),0,1),(B(0,2),B(1),3)]
pats[6] = [(B(0,1,3),0,1),(B(0,3),B(1),3)]
for k in (7,):
    st, sol, t = run(k, pats, 100); print(k, st, round(t,1)); print(show(k, sol) if sol else '')
