#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
echo $$ > run_gac.pid
until [ -f w14_gac_elim.json ]; do taskset -c 0 nice -n 10 python3 w14_gac.py >> w14_gac.log 2>&1 || sleep 5; done
