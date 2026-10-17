#!/bin/bash
# usage: w11n_go.sh BRANCH TAG [opts...]  (= w11_go.sh with PYTHONPATH; one <=1150 s chunk; appends to TAG.log)
export PYTHONPATH=work/e616/pylib:$PYTHONPATH
cd "$(dirname "$0")"; BR=$1; TAG=$2; shift 2
echo "== chunk $(date -u)" >> $TAG.log
timeout 1150 nice -n 2 python3 w11_exact.py $BR $TAG "$@" >> $TAG.log 2>&1
