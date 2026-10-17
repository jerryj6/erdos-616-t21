#!/bin/bash
# drop-one controls, after the main tree finishes. For each family: conflict matrix without it, then lazy SAT (cap 1200 s).
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
echo $$ > run_ctrl.pid
while [ ! -f w14_cert2_17917.done ]; do sleep 60; done
for f in A OO D1d SAME F1 L3; do
  export W14DROP=$f
  [ -f w14_conf_drop$f.npz ] || taskset -c 0 nice -n 10 python3 w14_conf.py > w14_conf_drop$f.log 2>&1
  [ -f w14_lazy_stall_drop$f.json ] || [ -f w14_lazy_drop$f.UNSAT ] || [ -f w14_ctrl_drop$f.timeout ] || { taskset -c 0 nice -n 10 timeout 1200 python3 w14_lazy.py > w14_lazy_drop$f.log 2>&1 || touch w14_ctrl_drop$f.timeout; }
  rm -f w14_reprows_drop$f.npy
done
touch w14_ctrl.DONE
