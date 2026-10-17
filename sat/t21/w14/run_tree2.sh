#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
echo $$ > run_tree2.pid
for r in 15116 14968 15954 16054 17917; do
  until [ -f w14_cert2_$r.done ]; do taskset -c 0 nice -n 10 python3 w14_tree2.py $r >> w14_tree2_$r.log 2>&1 || sleep 5; done
done
for r in 15116 14968 15954 16054 17917; do
  [ -f w14_cert2_$r.trim ] || { taskset -c 0 nice -n 10 ../../tools/drat-trim w14_cert2_$r.cnf w14_cert2_$r.drat -t 3000 > w14_cert2_$r.trim.tmp 2>&1; mv w14_cert2_$r.trim.tmp w14_cert2_$r.trim; }
  sha256sum w14_cert2_$r.cnf w14_cert2_$r.drat >> w14_cert2.sha256
done
