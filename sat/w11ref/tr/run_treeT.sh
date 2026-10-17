#!/bin/bash
# tree certificate for class TAG (plan + 1 tree per Stab(B*)-orbit + drat-trim + certcheck); resumable
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/../../t21/w14ref/pylib:$PWD/../../pylib; ulimit -v 2000000
T=$1; PY="taskset -c 0 nice -n 10 python3"
[ -f case_${T}_plan.json ] || $PY tr_case.py $T plan >> tree_$T.log 2>&1
NR=$(python3 -c "import json;print(len(json.load(open('case_${T}_plan.json'))['reps']))")
for K in $(seq 0 $((NR-1))); do
  N=tree_${T}_$K
  [ -f $N.drat ] || $PY tr_tree.py $T $K >> tree_$T.log 2>&1
  [ -f $N.drat ] && [ ! -f $N.trim ] && { taskset -c 0 nice -n 10 ../../tools/drat-trim $N.cnf $N.drat -t 20000 > $N.trim.tmp 2>&1; mv $N.trim.tmp $N.trim; echo "$N: $(grep -a 's [A-Z]' $N.trim | tr -d '\r') $(date -u)" >> tree_$T.log; }
done
[ -f certcheck$T.log ] || $PY tr_certcheck.py $T > certcheck$T.log 2>&1
echo "tree $T done $(date -u)" >> tree_$T.log
