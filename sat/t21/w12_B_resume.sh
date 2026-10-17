#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=work/e616/pylib
while pgrep -f 'w11_exact.py k4:3211 w12Br2' >/dev/null; do sleep 5; done
taskset -c 0 python3 w12_cegar.py B sel=11,12,15,16,21,22,23 maxrounds=40 >> w12_B_cegar.log 2>&1
