#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib
echo $$ > run_lazy.pid
until [ -f w14_lazy.UNSAT ] || [ -f w14_lazy_stall.json ]; do taskset -c 0 nice -n 10 python3 w14_lazy.py >> w14_lazy.log 2>&1 || sleep 5; done
