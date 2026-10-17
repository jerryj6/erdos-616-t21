#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
echo $$ > run_sac.pid
until [ -f w14_sac.DONE ]; do taskset -c 0 nice -n 10 python3 w14_sac.py >> w14_sac.log 2>&1 || sleep 5; done
