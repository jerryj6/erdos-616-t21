#!/bin/bash
# hedge: 8 root cases of Φ_33 (tr_case.py), each drat-trim'd; resumable
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/../../t21/w14ref/pylib:$PWD/../../pylib; ulimit -v 2000000
NI=${1:-10}
[ -f case_33_plan.json ] || taskset -c 0 nice -n $NI python3 tr_case.py 33 plan >> case.log 2>&1
NR=$(python3 -c "import json;print(len(json.load(open('case_33_plan.json'))['reps']))")
for K in $(seq 0 $((NR-1))); do
  N=case_33_$K
  [ -f $N.drat ] || taskset -c 0 nice -n $NI python3 tr_case.py 33 case $K >> case.log 2>&1
  [ -f $N.drat ] && [ ! -f $N.trim ] && { taskset -c 0 nice -n $NI ../../tools/drat-trim $N.cnf $N.drat -t 20000 > $N.trim.tmp 2>&1; mv $N.trim.tmp $N.trim; echo "$N: $(grep 's [A-Z]' $N.trim)" >> case.log; }
done
touch run_case.done
