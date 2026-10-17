#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=$PWD/../../t21/w14ref/pylib:$PWD/../../pylib; ulimit -v 2000000
for F in 0.3 0.15; do
  N=sub33_$F
  [ -f $N.cnf ] || { taskset -c 0 nice -n 19 python3 tr_sub.py 33 $F 7 $N.cnf.tmp >> subtry.log 2>&1 && mv $N.cnf.tmp $N.cnf; }
  [ -f $N.res ] || { taskset -c 0 nice -n 19 ../../tools/kissat -q --time=1500 $N.cnf $N.drat > $N.kout 2>&1; rc=$?; echo "$N rc=$rc $(date -u)" >> subtry.log; [ $rc = 20 ] && echo UNSAT > $N.res; [ $rc = 10 ] && { echo SAT > $N.res; rm -f $N.drat; }; }
  grep -q UNSAT $N.res 2>/dev/null && break
done
