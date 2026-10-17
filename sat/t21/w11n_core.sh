#!/bin/bash
export PYTHONPATH=work/e616/pylib:$PYTHONPATH
cd "$(dirname "$0")"; BR=$1; T=$2
timeout 1150 nice -n 2 python3 w10x_core.py $BR $T rounds=3 > ${T}_core.log 2>&1
echo "EXIT $? $(date -u)" >> ${T}_core.log
