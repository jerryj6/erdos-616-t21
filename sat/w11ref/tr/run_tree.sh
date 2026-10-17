#!/bin/bash
# primary (3,3) certificate: 8 root cases (Stab(B*) orbits), each a propagation+branching DRAT (tr_tree.py) checked by drat-trim
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/../../t21/w14ref/pylib:$PWD/../../pylib; ulimit -v 2000000
NI=${1:-10}
[ -f case_33_plan.json ] || taskset -c 0 nice -n $NI python3 tr_case.py 33 plan >> tree.log 2>&1
NR=$(python3 -c "import json;print(len(json.load(open('case_33_plan.json'))['reps']))")
for K in $(seq 0 $((NR-1))); do
  N=tree_33_$K
  [ -f $N.drat ] || taskset -c 0 nice -n $NI python3 tr_tree.py 33 $K >> tree.log 2>&1
  [ -f $N.drat ] && [ ! -f $N.trim ] && { taskset -c 0 nice -n $NI ../../tools/drat-trim $N.cnf $N.drat -t 20000 > $N.trim.tmp 2>&1; mv $N.trim.tmp $N.trim; echo "$N: $(grep -a 's [A-Z]' $N.trim | tr -d '\r') $(date -u)" >> tree.log; }
done
touch run_tree.done
