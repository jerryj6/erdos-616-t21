#!/bin/bash
# Wave 12 N-K4 tau-edges: one <=1150 s chunk of w11_exact.py on CPU 0. usage: w12_go.sh BRANCH TAG [opts...]
export PYTHONPATH=work/e616/pylib:$PYTHONPATH
cd "$(dirname "$0")"; BR=$1; TAG=$2; shift 2
echo "== chunk $(date -u)" >> $TAG.log
ulimit -v 2400000
timeout 1150 taskset -c ${W12CPU:-0} nice -n 2 python3 w11_exact.py $BR $TAG "$@" >> $TAG.log 2>&1
echo "== exit $? $(date -u)" >> $TAG.log
