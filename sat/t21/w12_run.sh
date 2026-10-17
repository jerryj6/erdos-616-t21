#!/bin/bash
# usage: w12_run.sh RUN sel=... [opts]  -- background CEGAR driver on CPU 0
cd "$(dirname "$0")"; export PYTHONPATH=work/e616/pylib
R=$1; shift
echo $$ > w12_$R.pid
taskset -c 0 python3 w12_cegar.py $R "$@" >> w12_${R}_cegar.log 2>&1
